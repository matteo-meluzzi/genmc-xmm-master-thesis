#include "config.h"
#include "Config.hpp"
#include "DepExecutionGraph.hpp"
#include "DriverHandlerDispatcher.hpp"
#include "Error.hpp"
#include "LLVMModule.hpp"
#include "Logger.hpp"
#include "GenMCDriver.hpp"
#include "Interpreter.h"
#include "GraphIterators.hpp"
#include "LabelVisitor.hpp"
#include "MaximalIterator.hpp"
#include "Parser.hpp"
#include "SExprVisitor.hpp"
#include "ThreadPool.hpp"
#include <llvm/IR/Verifier.h>
#include <llvm/Support/DynamicLibrary.h>
#include <llvm/Support/Format.h>
#include <llvm/Support/raw_os_ostream.h>

#include <algorithm>
#include <csignal>

/**
 * Adds to worklist all XMM backward revisits of sLab.
 * @param sLab the write we want to calculate the revisits for.
*/
bool GenMCDriver::calcXMMBackwardRevisits(const WriteLabel *sLab) 
{
	auto &g = getGraph();
	auto &currExe = execStack.back();

	auto loads = getRevisitableApproximation(sLab);

	GENMC_DEBUG( LOG(VerbosityLevel::Debug3) << "Revisitable: " << format(loads) << "\n"; );
	if (tryOptimizeRevisits(sLab, loads))
		return true;

	GENMC_DEBUG( LOG(VerbosityLevel::Debug3) << "Revisitable (optimized): " << format(loads) << "\n"; );
	for (auto &l : loads) {
		auto *rLab = g.getReadLabel(l);
		BUG_ON(!rLab);

		auto br = std::make_unique<BackwardXMMRevisit>(l, sLab->getPos(), getRevisitView(rLab, sLab), std::make_unique<ReadLabel>(*currExe.racyRead), std::make_unique<WriteLabel>(*currExe.racyWrite), currExe.val_addr_to_reads_in_graph, currExe.read_in_graph_to_val, currExe.committedEvents);
		if (!isMaximalExtension(*br))
			break;

		addToWorklist(sLab->getStamp(), std::move(br));
	}

	return checkAtomicity(sLab) && checkRevBlockHELPER(sLab, loads) && !isMoot();
}

/**
 * Calculates backward revisits for sLab. If the graph is XMM or XMM_HB_PREDS, calcXMMBackwardRevisits is called.
 * @param sLab the write we want to calculate the revisits for.
*/
bool GenMCDriver::calcRevisits(const WriteLabel *sLab)
{
	auto &g = getGraph();
	
	if (g.getKind() == GraphKind::XMM || g.getKind() == GraphKind::XMM_HB_PREDS) {
		return calcXMMBackwardRevisits(sLab);
	}

	auto loads = getRevisitableApproximation(sLab);

	GENMC_DEBUG( LOG(VerbosityLevel::Debug3) << "Revisitable: " << format(loads) << "\n"; );
	if (tryOptimizeRevisits(sLab, loads))
		return true;

	GENMC_DEBUG( LOG(VerbosityLevel::Debug3) << "Revisitable (optimized): " << format(loads) << "\n"; );
	for (auto &l : loads) {
		auto *rLab = g.getReadLabel(l);
		BUG_ON(!rLab);

		auto br = constructBackwardRevisit(rLab, sLab);
		if (!isMaximalExtension(*br))
			break;

		addToWorklist(sLab->getStamp(), std::move(br));
	}

	return checkAtomicity(sLab) && checkRevBlockHELPER(sLab, loads) && !isMoot();
}

/**
 * Called during execution when a stored event is added to the graph.
 * @param wLab the write event that is being added to the graph.
*/
void GenMCDriver::handleStore(std::unique_ptr<WriteLabel> wLab)
{
	auto &g = getGraph();
	auto *EE = getEE();
	if (isExecutionDrivenByGraph(&*wLab)) {
		return;
	}

    auto &currExe = execStack.back();

	if (g.isRMWStore(&*wLab)) {
		if (auto *rPrev = g.getReadLabel(wLab->getPos().prev())) {
			if (!rPrev->getRf()) {
				// if wLab is a RMW store, and its read is not reading from anywhere 
				// block the current thread until that read will have a rf edge.
				getEE()->getCurThr().block(BlockageType::Confirmation);
				return;
			}
		}
	}

	/* If it's a valid access, track coherence for this location */
	g.trackCoherenceAtLoc(wLab->getAddr());

	if (getConf()->helper && g.isRMWStore(&*wLab))
		annotateStoreHELPER(&*wLab);

	auto *lab = llvm::dyn_cast<WriteLabel>(addLabelToGraph(std::move(wLab)));

	if (!isAccessValid(lab)) {
		reportError(lab->getPos(), VerificationError::VE_AccessNonMalloc);
		return;
	}
	g.addAlloc(findAllocatingLabel(g, lab->getAddr()), lab);

	/* It is always consistent to add the store at the end of MO */
	if (llvm::isa<BIncFaiWriteLabel>(lab) && lab->getVal() == SVal(0))
		lab->setVal(getBarrierInitValue(lab->getAccess()));

	calcCoOrderings(lab);

	/* If the graph is not consistent (e.g., w/ LAPOR) stop the exploration */
	bool cons = g.getKind() != GraphKind::GenMC || ensureConsistentStore(lab);

	GENMC_DEBUG( LOG(VerbosityLevel::Debug2)
		     << "--- Added store " << lab->getPos() << "\n" << getGraph(); );

	if (cons && checkForRaces(lab) != VerificationError::VE_OK)
		return;

	if (currExe.isXMM) {
		// Perform matching of XMM bottom reads to the currently added WriteLabel
		auto wVal = lab->getVal().get(); // value written by lab
		auto wAddr = lab->getAddr();
		auto tid = lab->getThread();
		if (currExe.val_addr_to_reads_in_graph.count({wAddr, wVal, tid}) > 0) { // if there are reads with the same variable and value
			auto &reads = currExe.val_addr_to_reads_in_graph[{wAddr, wVal, tid}];
			for (auto readEvent : reads) {	
				auto *readLab = g.getReadLabel(readEvent);
				assert(readLab);

				if (!readLab->getRf())
					g.changeRf(readEvent, lab->getPos()); // set each of the reads to read from lab
				else if (!areInLoadBufferingRace(readLab, lab)) {
					// readLab has already been matched with a po-previous write.
					// we need to push a revisit to ensure that this write is also read-from.
					// since readLab is committed, it's easy we just have to change the rf edge in the final graph.
					// Optimization: check that readLab and lab are not in LB race, since in that case a lbRaceXMMRevisit would be pushed to worklist anyways.
					auto rev = std::make_unique<CommittedWriteXMMRevisit>(readEvent, lab->getPos(), std::make_unique<ReadLabel>(*currExe.racyRead), std::make_unique<WriteLabel>(*currExe.racyWrite), currExe.committedEvents);
					addToWorklist(std::numeric_limits<uint32_t>::max(), std::move(rev));
				}
				currExe.committedEvents.insert(lab->getPos());

				if (g.isRMWLoad(readEvent)) {
					// if readEvent is RMW, its thread may have been blocked until it
					// received a rf edge. So we unblock it now.
					getEE()->getThrById(readEvent.thread).unblock();
				}
			}
		}
	}

	if (!inRecoveryMode() && !inReplay())
		calcRevisits(lab);

	if (!cons)
		return;

	checkReconsiderFaiSpinloop(lab);
	if (llvm::isa<HelpedCasWriteLabel>(lab))
		unblockWaitingHelping();

	/* Check for races */
	if (llvm::isa<UnlockWriteLabel>(lab))
		checkUnlockValidity(lab);
	if (llvm::isa<BInitWriteLabel>(lab))
		checkBInitValidity(lab);
	checkFinalAnnotations(lab);
}

/**
 * Called during execution when a read event is added to the graph.
 * @param rLab the read event that is being added to the graph.
 * @return an Some(x) if rLab should be added to the graph, and reads value x. None if rLab should not be added to the graph.
*/
std::optional<SVal> GenMCDriver::handleLoad(std::unique_ptr<ReadLabel> rLab)
{
	auto &g = getGraph();
	auto *EE = getEE();
	auto &thr = EE->getCurThr();
	auto &currExe = execStack.back();

	if (inRecoveryMode() && rLab->getAddr().isVolatile())
		return {getRecReadRetValue(rLab.get())};

	if (isExecutionDrivenByGraph(&*rLab)) {
		auto *rLabInGraph = llvm::dyn_cast<ReadLabel>(g.getEventLabel(rLab->getPos()));
		if (!rLabInGraph) {
			// if rLab was not found it means that this execution is not possible
			// this can happen during a XMM+HB PREDS execution
			getEE()->block();
			return {};
		}
		assert(rLabInGraph);
		if (currExe.isXMM && currExe.read_in_graph_to_val.count(rLabInGraph->getPos())) {
			// if this is a read that has no rf edge in the graph
			// we return the value it used to read before making the XMM graph copy
			return { currExe.read_in_graph_to_val[rLabInGraph->getPos()] };
		} else {
			// otherwise behave normally
			return { getReadRetValueAndMaybeBlock(rLabInGraph) };
		}
	}

	/* First, we have to check whether the access is valid. This has to
	 * happen here because we may query the interpreter for this location's
	 * value in order to determine whether this load is going to be an RMW.
	 * Coherence needs to be tracked before validity is established, as
	 * consistency checks may be triggered if the access is invalid */
	g.trackCoherenceAtLoc(rLab->getAddr());

	if (!rLab->getAnnot())
		rLab->setAnnot(EE->getCurrentAnnotConcretized());
	cacheEventLabel(&*rLab);
	auto *lab = llvm::dyn_cast<ReadLabel>(addLabelToGraph(std::move(rLab)));

	if (!isAccessValid(lab)) {
		reportError(lab->getPos(), VerificationError::VE_AccessNonMalloc);
		return std::nullopt; /* This execution will be blocked */
	}
	g.addAlloc(findAllocatingLabel(g, lab->getAddr()), lab);

	if (checkForRaces(lab) != VerificationError::VE_OK)
		return std::nullopt;

	/* Get an approximation of the stores we can read from */
	auto stores = getRfsApproximation(lab);
	if (stores.empty()) {
		EE->block();
		return {};
	}
	GENMC_DEBUG( LOG(VerbosityLevel::Debug3) << "Rfs: " << format(stores) << "\n"; );

	/* Try to minimize the number of rfs */
	if (!filterOptimizeRfs(lab, stores))
		return std::nullopt;

	/* ... add an appropriate label with a random rf */
	g.changeRf(lab->getPos(), stores.back());
	GENMC_DEBUG( LOG(VerbosityLevel::Debug3) << "Rfs (optimized): " << format(stores) << "\n"; );

	/* ... and make sure that the rf we end up with is consistent */
	if (g.getKind() == GraphKind::GenMC && !ensureConsistentRf(lab, stores))
		return std::nullopt;

	if (readsUninitializedMem(lab)) {
		reportError(lab->getPos(), VerificationError::VE_UninitializedMem);
		return std::nullopt;
	}

	GENMC_DEBUG(
		LOG(VerbosityLevel::Debug2)
		<< "--- Added load " << lab->getPos() << "\n" << getGraph();
	);

	/* Check whether the load forces us to reconsider some existing event */
	checkReconsiderFaiSpinloop(lab);

	/* Check for races and reading from uninitialized memory */
	if (llvm::isa<LockCasReadLabel>(lab))
		checkLockValidity(lab, stores);
	if (llvm::isa<BIncFaiReadLabel>(lab))
		checkBIncValidity(lab, stores);

	if (isRescheduledRead(lab->getPos()))
		setRescheduledRead(Event::getInit());

	/* If this is the last part of barrier_wait() check whether we should block */
	auto retVal = getWriteValue(g.getEventLabel(stores.back()), lab->getAccess());
	if (llvm::isa<BWaitReadLabel>(lab) &&
	    retVal != getBarrierInitValue(lab->getAccess())) {
		if (!getConf()->disableBAM) {
			auto pos = lab->getPos();
			g.removeLast(pos.thread);
			blockThread(pos, BlockageType::Barrier);
			return {retVal};
		}
		getEE()->getCurThr().block(BlockageType::Barrier);
	}

	/* Push all the other alternatives choices to the Stack (many maximals for wb) */
	std::for_each(stores.begin(), stores.end() - 1, [&](const Event &s){
		auto status = false; /* MO messes with the status */
		if (g.getKind() == GraphKind::GenMC) {
			// if the current graph is not XMM, we only need a simple ForwardRevisit.
			addToWorklist(lab->getStamp(), std::make_unique<ReadForwardRevisit>(lab->getPos(), s, status));
		}
		else {
			assert(currExe.isXMM);
			// if the current graph is XMM, we need to remember the information about bottom reads contained in currExe.val_addr_to_reads_in_graph and currExe.read_in_graph_to_val
			// We push a ReadForwardXMMRevisit by copying this information from the current execution.
			auto frXMM = std::make_unique<ReadForwardXMMRevisit>(lab->getPos(), s, std::make_unique<ReadLabel>(*currExe.racyRead), std::make_unique<WriteLabel>(*currExe.racyWrite), currExe.val_addr_to_reads_in_graph, currExe.read_in_graph_to_val, currExe.committedEvents);
			addToWorklist(lab->getStamp(), std::move(frXMM));
		}
	});
	return {retVal};
}

/**
 * Returns true if eLab1 is before eLab2 in the eco relation
 * eco = rf + (co ; rf^?) + (fr ; rf^?)
*/
bool GenMCDriver::isEcoBefore(const EventLabel *eLab1, const EventLabel *eLab2) const {
	auto &g = getGraph();
	if (auto *rLab2 = g.getReadLabel(eLab2->getPos())) {
		if (rLab2->getRf() == eLab1) {
			return true;
		}
	} 
	if (std::find_if(co_succ_begin(g, eLab1), co_succ_end(g, eLab1), [&](const WriteLabel &e) { 
			if (auto *rLab2 = llvm::dyn_cast<ReadLabel>(eLab2)) {
				if (rLab2->getRf() == &e) {
					return true;
				}
			}
			return &e == eLab2; 
		}) != co_succ_end(g, eLab1)) {
		return true;
	}
	if (std::find_if(fr_succ_begin(g, eLab1), fr_succ_end(g, eLab1), [&](const WriteLabel &e) {
		if (auto *rLab2 = llvm::dyn_cast<ReadLabel>(eLab2)) {
			if (rLab2->getRf() == &e) {
				return true;
			}
		}
		return &e == eLab2;
	}) != fr_succ_end(g, eLab1)) {
		return true;
	}
	return false;
}

/**
 * Calculates if g has a cycle starting from currentEventLabel using DFS.
 * @param g an ExecutionGraph.
 * @param currentEventLabel the event where we start looking from a cycle from.
 * @param visited a set of event labels which have been visited.
 * @param deadEvents a set of event labels which we know do not lead to a cycle.
 * @return true if g has a cycle starting from currentEventLabel.
*/
bool hasCycle(const ExecutionGraph &g, const EventLabel *currentEventLabel, std::unordered_set<const EventLabel *> &visited, std::unordered_set<const EventLabel *> &deadEnds)
{
	if (visited.contains(currentEventLabel)) 
		return true;
	if (deadEnds.contains(currentEventLabel))
		return false;
	deadEnds.insert(currentEventLabel);

	visited.insert(currentEventLabel);
	auto prevEventLabel = g.getPreviousLabel(currentEventLabel);
	if (prevEventLabel) {
		if (hasCycle(g, prevEventLabel, visited, deadEnds)) {
			return true;
		}
	}

	if (auto *rLab = llvm::dyn_cast<ReadLabel>(currentEventLabel)) {
		if (auto *rf = rLab->getRf()) {
			if (hasCycle(g, rf, visited, deadEnds)) {
				return true;
			}
		}
	}
	visited.erase(currentEventLabel);

	return false;
}

/**
 * Calculates if the dataFlow of uncommitted events forms a cycle. Used for determining whether uncommitted events are stable (definition 10).
 * @param dataFlow a vector[tid][set of tids]. dataFlow[tid] represents which threads are reacheable from tid.
 * @param currentTid the tid that is currently being visited.
 * @param visitedTids a set of tids that have been visited already.
 * @param previouslyCheckedTids a set of tids that have already been checked and do not cycle back.
 * @return true if dataFlow cycles back to a previous thread.
*/
bool cyclesBackToThread(const std::vector<std::unordered_set<unsigned int>> &dataFlow, unsigned int currentTid, std::unordered_set<unsigned int> &visitedTids, std::unordered_set<unsigned int> &previouslyCheckedTids)
{
	if (previouslyCheckedTids.contains(currentTid)) {
		return false;
	}
	if (visitedTids.contains(currentTid)) {
		return true;
	}
	visitedTids.insert(currentTid);
	for (const auto next_tid : dataFlow[currentTid]) {
		if (cyclesBackToThread(dataFlow, next_tid, visitedTids, previouslyCheckedTids)) {
			return true;
		}
	}
	previouslyCheckedTids.insert(currentTid);
	visitedTids.erase(currentTid);
	return false;
}

/**
 * Builds the data flow given a set of uncommitted events. Used for determining whether uncommitted events are stable (definition 10).
 * @param g an ExecutionGraph
 * @param committedEvents a set of Event that are committed.
 * @return a dataFlow: vector[tid][set of tids]. dataFlow[tid] represents which threads are reacheable from tid.
*/
std::vector<std::unordered_set<unsigned int>> constructDataFlowOfUncommittedEvents(const ExecutionGraph &g, const std::unordered_set<Event, EventHasher> &committedEvents) {
	std::vector<std::unordered_set<unsigned int>> dataFlow(g.getNumThreads());
	for (auto tid = 0; tid < g.getNumThreads(); tid++) {
		for (auto index = 0; index < g.getThreadSize(tid); index++) {
			if (auto *uncommittedRLab = g.getReadLabel({tid, index})) {
				if (committedEvents.contains(uncommittedRLab->getPos()))
					continue;
				if (auto *rf = llvm::dyn_cast<WriteLabel>(uncommittedRLab->getRf())) {
					if (rf->getThread() != tid) {
						dataFlow[tid].insert(rf->getThread());
					} 
				}
			}
		}
	}
	return dataFlow;
}

/**
 * Calculates whether uncommitted events are stable according to definition 10. 
 * @param g an ExecutionGraph.
 * @return true if the uncommitted events are stable (their data flow does not form a cycle). 
*/
bool GenMCDriver::areXMMUncommittedReadsStable(const ExecutionGraph &g) const {
	assert(execStack.back().isXMM);
	auto dataFlow = constructDataFlowOfUncommittedEvents(g, execStack.back().committedEvents);
	std::unordered_set<unsigned int> previouslyCheckedTids;

	for (auto tid = 0; tid < g.getNumThreads(); tid++) {		
		std::unordered_set<unsigned int> visitedTids;
		if (cyclesBackToThread(dataFlow, tid, visitedTids, previouslyCheckedTids)) {
			return false;
		}
		assert(visitedTids.empty());
	}
	return true;
}

bool areWriteLabelsEquivalent(const WriteLabel *w1, const WriteLabel *w2) {
	return w1->getAddr() == w2->getAddr() && w1->getVal() == w2->getVal() && w1->getOrdering() == w2->getOrdering();
}

const WriteLabel *findEquivalentWrite(const ExecutionGraph &g, const ReadLabel *racyRead, const WriteLabel *wLab) {
	auto racyReadTID = racyRead->getThread();
	for (auto index = racyRead->getIndex(); index < g.getThreadSize(racyReadTID); index++) {
		if (auto *w = g.getWriteLabel({racyReadTID, index})) {
			if (areWriteLabelsEquivalent(wLab, w)) {
				return w;
			}
		}
	}
	return nullptr;
}

/**
 * Determines whether G' is embeddedSubgraph of G, given committed events C
 * 
 * @param g is G'
 * @param g_original is G
 * @param racyRead is the LB racy read
 * @param committedEvents is C
 * 
 * Performs mo check:
 * mo relation between committed events should be preserved from G to G'
 * 
 * Performs rpo check:
 * rpo relation between committed events should be preserved from G to G'
 */
bool embeddedSubgraph(const ExecutionGraph &g, const ExecutionGraph &g_original, const ReadLabel *racyRead, const std::unordered_set<Event, EventHasher> &committedEvents)
{
	auto racyReadTID = racyRead->getThread();

	bool hasRpoEdge = false;
	std::unordered_set<SAddr> relAddrsBefore;
	for (auto index = racyRead->getIndex(); index < g.getThreadSize(racyReadTID); index++) {
		// rpo check:
		auto *eLab = g.getEventLabel({racyReadTID, index});
		if (eLab->getOrdering() == llvm::AtomicOrdering::Acquire) {
			hasRpoEdge = true;
		}
		if (eLab->getOrdering() == llvm::AtomicOrdering::Release) {
			if (auto *w = llvm::dyn_cast<WriteLabel>(eLab)) {
				relAddrsBefore.insert(w->getAddr());
			}
			else {
				hasRpoEdge = true;
			}
		}

		if (auto *w = g.getWriteLabel({racyReadTID, index})) {
			if (committedEvents.contains(w->getPos())) {
				// rpo check:
				if (hasRpoEdge) {
					return false;
				}
				if (relAddrsBefore.contains(w->getAddr())) {
					return false;
				}

				// mo check:
				if (auto *w_original = findEquivalentWrite(g_original, racyRead, w)) {
					auto mo_prefix_it = g.co_pred_begin(w);
					auto mo_original_prefix_it = g_original.co_pred_begin(w_original);
					while (mo_prefix_it != g.co_pred_end(w) && mo_original_prefix_it != g_original.co_pred_end(w_original)) {
						auto &w1 = *mo_prefix_it;
						auto &w2 = *mo_original_prefix_it;
						if (w1.getThread() == racyReadTID && w1.getIndex() >= racyRead->getIndex()) {
							mo_prefix_it++;
							continue;
						}
						if (w2.getThread() == racyReadTID && w2.getIndex() >= racyRead->getIndex()) {
							mo_original_prefix_it++;
							continue;
						}
						if (!areWriteLabelsEquivalent(&w1, &w2)) {
							return false;
						}
						mo_prefix_it++;
						mo_original_prefix_it++;
					}
				}			
			}
		} 
	}

	return true;
}

/**
 * Determines whether the current graph is consistent.
 * 
 * If any read is reading from BOTTOM, returns false.
 * 
 * Coherence check:
 * there must be no events x and y, such that x -- hb --> y and y -- eco --> x
 * 
 * Definition 10 check:
 * Uncommitted events must be stable
 * 
 * Optimization check:
 * XMM executions must be cyclic in order to avoid having to hash RC11 executions.
*/
bool GenMCDriver::xmmExecutionConsistent() const
{	
	auto &g = getGraph();

	// Bottom reads check: do all reads have a rf edge? if not, the graph is not consistent.
	for (auto tid = 0; tid < g.getNumThreads(); tid++) {
		for (auto index = 0; index < g.getThreadSize(tid); index++) {
			if (auto *rLab = g.getReadLabel({tid, index})) {
				if (!rLab->getRf()) {
					return false;
				}
			}
		}
	}

	// Coherence check: there is no such x and y events, such that x -- hb --> y and y -- eco --> x. 
	for (auto tid1 = 0; tid1 < g.getNumThreads(); tid1++) {
		for (auto index1 = 0; index1 < g.getThreadSize(tid1); index1++) {
			for (auto tid2 = 0; tid2 < g.getNumThreads(); tid2++) {
				for (auto index2 = 0; index2 < g.getThreadSize(tid2); index2++) {
					auto eLab1 = g.getEventLabel({tid1, index1});
					auto eLab2 = g.getEventLabel({tid2, index2});
					
					// eLab1 --hb--> eLab2 && eLab2 --eco--> eLab1
					if (getHbView(eLab2).contains(eLab1->getPos()) && isEcoBefore(eLab2, eLab1)) {
						return false;
					}
				}
			}
		}
	}

	auto &currExe = execStack.back();
	assert(currExe.isXMM);
	if (!areXMMUncommittedReadsStable(g)) {
		return false;
	}

	assert(execStack.size() > 1); // there must be a graph from which we derived the current graph
	auto &originalGraph = *execStack[execStack.size() - 2].graph;
	if (!embeddedSubgraph(g, originalGraph, currExe.racyRead.get(), currExe.committedEvents)) {
		return false;
	}

	// Optimization: XMM graphs should have a cycle, so that RC11 executions do not need to be checked for duplicates
	std::unordered_set<const EventLabel *> deadEnds;
	bool cycleFound = false;
	for (auto tid = 0; tid < g.getNumThreads(); tid++) {
		if (g.getThreadSize(tid) == 0)
			continue;
		std::unordered_set<const EventLabel *> visited;
		auto *eLab = g.getLastThreadLabel(tid);
		assert(eLab);
		if (hasCycle(g, eLab, visited, deadEnds)) {
			cycleFound = true;
			break;
		}
		assert(visited.empty());
	}

	return cycleFound;
}

/**
 * Called when the execution step ends.
*/
void GenMCDriver::handleExecutionEnd()
{
	/* LAPOR: Check lock-well-formedness */
	if (getConf()->LAPOR && !isLockWellFormedLAPOR())
		WARN_ONCE("lapor-not-well-formed", "Execution not lock-well-formed!\n");

	if (isMoot()) {
		GENMC_DEBUG( ++result.exploredMoot; );
		return;
	}

	/* Helper: Check helping CAS annotation */
	if (getConf()->helper)
		checkHelpingCasAnnotation();

	/* Ignore the execution if some assume has failed */
	if (isExecutionBlocked()) {
		++result.exploredBlocked;
		if (getConf()->printBlockedExecs)
			printGraph();
		if (getConf()->checkLiveness)
			checkLiveness();
		return;
	}

	assert(execStack.size() > 0);
	if (!execStack.back().isXMM || (execStack.back().isXMM && xmmExecutionConsistent())) {
		auto &currExe = execStack.back();
		bool isDup = false;
		auto &g = getGraph();

		if (currExe.isXMM) { // If XMM execution, check that it's not a duplicate
			isDup = isDupElseAdd(getGraph());
		}

		if (!isDup) {
			if (getConf()->printExecGraphs && !getConf()->persevere)
				printGraph(); /* Delay printing if persevere is enabled */		
			
			if (outputDotGraphFileStream.has_value()) {
				dotPrintGraph(*outputDotGraphFileStream);
			}
			++result.explored;
			
			/* XMM: push additional revisits if xmm is enabled */
			if (getConf()->XMM) {
				calcXMMRevisitsLbRace();
			}
			if (getConf()->XMM && g.getKind() == XMM) {
				calcXMMRevisitsHbPredecessors();
				calcXMMRevisitsLBRacyReadThread();
			}
		} else {
			// Duplicate execution
			result.duplicates++;
			// llvm::dbgs() << "found a duplicate graph\n";
			// printGraph();
		}
	} else {
		// Invalid execution
		result.exploredBlocked++;
		// llvm::dbgs() << "found an invalid graph\n";
		// printGraph();
	}

	if (getConf()->realTimeOutput) {
		llvm::dbgs() << "\x1B[2J\x1B[H"; // clear terminal
		llvm::dbgs() << "Explored: " << result.explored << "\nDuplicates: " << result.duplicates << "\nBlocked: " << result.exploredBlocked << "\n";
	}
	
    return;
}

/** 
 * Called to explore all execution graphs.
*/
void GenMCDriver::explore()
{
	auto *EE = getEE();

	resetExplorationOptions();
	EE->setExecutionContext(createExecutionContext(getGraph()));
	while (!isHalting()) {
		EE->reset();

		/* Get main program function and run the program */
		EE->runAsMain(getConf()->programEntryFun);
		if (getConf()->persevere)
			EE->runRecovery();

		auto validExecution = false;
		while (!validExecution) {
			/*
			 * restrictAndRevisit() might deem some execution infeasible,
			 * so we have to reset all exploration options before
			 * calling it again
			 */
			resetExplorationOptions();

			auto [stamp, item] = getNextItem();
			if (!item) {
				if (popExecution())
					continue;
				return;
			}
			auto pos = item->getPos();
			validExecution = restrictAndRevisit(stamp, std::move(item)) && isRevisitValid(pos);
		}
	}
}

/**
 * Constructs a XMM execution.
 * Computes metadata which value the reads from bottom from the original graph should read.
 * This information is stored in two hash maps:
 * - val_addr_to_read: pair[value, variable] -> set[ReadLabel *]
 * - read_to_val: ReadLabel * -> value
 * Computes committed events:
 * - all events in og are committed except revisitPos, since its rf edge changes in og compared to in g.
 * 
 * @param g the original graph.
 * @param og a restricted copy of g.
 * @param revisitPos the Event whose rf edge we are changing in og compared to the original graph g.
 * @param racyRead the LB racy read (for LBRaceXMMRevisits this is the same as revisitPos).
 * @param racyWrite the LB racy write.
*/
GenMCDriver::Execution GenMCDriver::constructXMMExecution(const ExecutionGraph &g, std::unique_ptr<ExecutionGraph> og, Event revisitPos, std::unique_ptr<ReadLabel> racyRead, std::unique_ptr<WriteLabel> racyWrite) {
	ValAddrTidToReadsMap val_addr_to_read;
	ReadToValMap read_to_val;
	// fill the necessary information in val_addr_to_read and read_to_val
	for (auto tid = 0; tid < og->getNumThreads(); tid++) {
		for (auto index = 0; index < og->getThreadSize(tid); index++) {
			if (auto *rLab = og->getReadLabel({tid, index})) {
				if (!rLab->getRf()) {
					auto originalRead = g.getReadLabel({tid, index});
					assert(originalRead);
					auto val = getReadValue(originalRead);
					read_to_val[rLab->getPos()] = val.get();
					val_addr_to_read[{rLab->getAddr(), val.get(), originalRead->getRf()->getThread()}].insert(rLab->getPos());
				}
			}
		}
	}

	auto committedEvents = addAllEventsToSet(*og);
	auto racyReadG = g.getReadLabel(revisitPos);
	auto racyReadOg = og->getReadLabel(revisitPos);
	if (getReadValue(racyReadG) != getReadValue(racyReadOg) || racyReadG->getRf()->getThread() != racyReadOg->getRf()->getThread())
		committedEvents.erase(revisitPos); // the racy read is the only event in og that might not be committed
	auto exe = Execution(std::move(og), LocalQueueT(), std::move(racyRead), std::move(racyWrite), std::move(val_addr_to_read), std::move(read_to_val), std::move(committedEvents));
	return std::move(exe);
}

/**
 * Called when a LBRaceXMMRevisit is popped from the worklist.
 * This function creates a restricted copy of the current graph.
 * A new Execution is pushed to the woklist with the constructXMMExecution method. 
*/
bool GenMCDriver::lbRaceXMMRevisit(std::unique_ptr<LBRaceXMMRevisit> lbRev) {
    auto &g = getGraph();
    auto *rLab = g.getReadLabel(lbRev->getPos());
    auto *wLab = g.getWriteLabel(lbRev->getRev());

    auto suffixView = calcLBRaceKeptEventsXMM(g, rLab);
    auto og = g.getCopyUpTo(suffixView);
    // change rLab to read from bottom in the new graph
    og->changeRf(rLab->getPos(), wLab->getPos());
	og->setKind(GraphKind::XMM);
	auto &racyWritePrefixView = getPrefixView(wLab);

	if (isDupElseAdd(*og)) {
		return false;
	}

    pushExecution(constructXMMExecution(g, std::move(og), rLab->getPos(),  std::move(lbRev->getRacyRead()), std::move(lbRev->getRacyWrite())));

    return true; // execution is valid
}

/**
 * Used for XMM HB PREDS revisits.
 * Calculates the Po+Rf prefix of eLab. The result is stored in the argument VectorClockView result.
 * This function is useful when there is a Po+Rf cycle in the graph and the standard EventLabel->getPrefixView() does not work.
 * 
 * @param g is the ExecutionGraph we are considering.
 * @param eLab is the event whose Po+Rf prefix we want to compute 
 * @param visited should be passed an empty set, it is used to remember which events have been visited in recursive calls.
 * @param result vector clock where the po+rf prefix is stored.
*/
void calcPoRf(const ExecutionGraph &g, const EventLabel *eLab, std::unordered_set<const EventLabel *> &visited, View &result) {
	if (visited.count(eLab) > 0)
		return;

	result.updateIdx(eLab->getPos());
	visited.insert(eLab);
	
	if (auto *rLab = llvm::dyn_cast<ReadLabel>(eLab)) {
		if (rLab->getRf()) {
			calcPoRf(g, rLab->getRf(), visited, result);
		}
	}

	auto *pred = g.getPreviousLabel(eLab);
	if (pred) {
		calcPoRf(g, pred, visited, result);
	}
}

/**
 * Called when a XMM HB PREDS revisit is popped from the worklist.
 * Creates a copy of the current graph up until the Po+Rf prefix of the LB cycle computed with calcPoRf.
 * A new execution is pushed to the worklist with the constructXMMExecution method.
*/
bool GenMCDriver::hbPredsXMMRevisit(std::unique_ptr<HbPredsXMMRevisit> hbRev) {	
	auto &g = getGraph();
	assert(g.getKind() == GraphKind::XMM);
	auto *rLab = g.getReadLabel(hbRev->getPos());
    auto *wLab = g.getWriteLabel(hbRev->getRev());

	View cyclePrefixView;
	std::unordered_set<const EventLabel *> visited;
	calcPoRf(g, rLab, visited, cyclePrefixView);
	cyclePrefixView.updateIdx(Event(0, g.getThreadSize(0)-1));

	auto og = g.getCopyUpTo(cyclePrefixView);
	og->setKind(GraphKind::XMM_HB_PREDS);

	if (isDupElseAdd(*og)) {
		return false;
	}

    pushExecution(constructXMMExecution(g, std::move(og), rLab->getPos(), std::make_unique<ReadLabel>(*execStack.back().racyRead), std::make_unique<WriteLabel>(*execStack.back().racyWrite)));

	return true;
}

/**
 * Called when a ReadForwardRacyReadTidXMMRevisit revisit is popped from the worklist.
 * The po-suffix of the reivisiting read is dropped.
 * A new Execution is created with the constructXMMExecution method.
*/
bool GenMCDriver::forwardRacyReadTidXMMRevisit(std::unique_ptr<ReadForwardRacyReadTidXMMRevisit> fr) {
	auto &g = getGraph();

	auto *rLab = g.getReadLabel(fr->getPos());
	auto *racyWrite = g.getWriteLabel(fr->getRacyWrite()->getPos());
	auto *revWrite = g.getEventLabel(fr->getRev());

	assert(revWrite->getThread() != rLab->getThread());

	auto suffixView = calcLBRaceKeptEventsXMM(g, rLab);
	
    auto og = g.getCopyUpTo(suffixView);
	og->setKind(GraphKind::XMM);
	assert(og->getNumThreads() > revWrite->getThread());
	assert(og->getThreadSize(revWrite->getThread()) > revWrite->getIndex());

	auto *newRf = og->getEventLabel(revWrite->getPos());
	assert(newRf);
	og->changeRf(rLab->getPos(), newRf->getPos());

	if (isDupElseAdd(*og)) {
		return false;
	}
	
	pushExecution(constructXMMExecution(g, std::move(og), rLab->getPos(), std::move(fr->getRacyRead()), std::move(fr->getRacyWrite())));

	return true;
}

/**
 * Called when a forward XMM revisit is popped from the worklist.
 * The current graph is not copied but instead is modified.
 * The XMM metadata is copied from fr to the current execution.
*/
bool GenMCDriver::forwardXMMRevisit(std::unique_ptr<ReadForwardXMMRevisit> fr) {
	auto &g = getGraph();
	auto committed = std::move(fr->committedEvents);
	auto *posLab = g.getReadLabel(fr->getPos());
	auto *revLab = g.getEventLabel(fr->getRev());
	if (getReadValue(posLab) != getWriteValue(revLab, posLab->getAccess()))
		committed.erase(fr->getPos());
	g.changeRf(fr->getPos(), fr->getRev());
	execStack.back().val_addr_to_reads_in_graph = std::move(fr->val_addr_to_reads_in_graph);
	execStack.back().read_in_graph_to_val = std::move(fr->read_in_graph_to_val);
	execStack.back().committedEvents = std::move(committed);
	return true;
}

/**
 * Called when a backward XMM revisit is popped from the worklist.
 * The current graph is restricted as if it were a normal RC11 backward revisit.
 * The XMM metadata is copied from fr to the new execution.
*/
bool GenMCDriver::backwardXMMRevisit(std::unique_ptr<BackwardXMMRevisit> br)
{
	auto &g = getGraph();

	/* Recalculate the view because some B labels might have been
	 * removed */
	auto *posLab = g.getReadLabel(br->getPos());
	auto *revLab = g.getWriteLabel(br->getRev());
    auto v = getRevisitView(posLab,
                            revLab,
                            nullptr);
	// This is needed for szymanski test to not crash, TODO: find out why v can be bigger than g in some cases.
	for (auto tid = 0; tid < g.getNumThreads(); tid++) 
		if (v->getMax(tid) >= g.getThreadSize(tid))
			return false;
	
	auto og = copyGraph(static_cast<BackwardRevisit *>(br.get()), &*v);
	og->setKind(GraphKind::XMM);

	auto val_addr_to_reads_in_graph = std::move(br->val_addr_to_reads_in_graph);
	std::erase_if(val_addr_to_reads_in_graph, [&](auto &item) {
		auto &reads = item.second;
		std::erase_if(reads, [&](auto &readEvent) {
			return !og->containsPos(readEvent);
		});
		return reads.empty();
	});

	auto read_in_graph_to_val = std::move(br->read_in_graph_to_val);
	std::erase_if(read_in_graph_to_val, [&](const auto &item) {
		auto read = item.first;
		return !og->containsPos(read);
	});

	auto committed = std::move(br->committedEvents);
	std::erase_if(committed, [&](const auto &item) {
		return !og->containsPos(item);
	});
	if (getReadValue(posLab) != getWriteValue(revLab)) {
		for (auto pos = br->getPos(); pos.index < og->getThreadSize(pos.thread); pos = Event(pos.thread, pos.index + 1)) {
			committed.erase(pos);
		}
	}
	auto exe = Execution(std::move(og), LocalQueueT(), std::move(br->getRacyRead()), std::move(br->getRacyWrite()), std::move(val_addr_to_reads_in_graph), std::move(read_in_graph_to_val), std::move(committed));
	pushExecution(std::move(exe));

	repairDanglingReads();
	revisitRead(*br);

	/* If there are idle workers in the thread pool,
	 * try submitting the job instead */
	auto *tp = getThreadPool();
	if (tp && tp->getRemainingTasks() < 8 * tp->size()) {
		if (isRevisitValid(br->getPos()))
			tp->submit(extractState());
		return false;
	}
	return true;
}

bool GenMCDriver::committedWriteXMMRevisit(std::unique_ptr<CommittedWriteXMMRevisit> rev) {
	// we should clone the current graph because we are changing a rf edge.
	auto og = getGraph().clone();
	// since the read we are revisiting is committed, we don't need to restrict the graph, so that is nice.
	og->changeRf(rev->getPos(), rev->getRev());

	auto committed = rev->committedEvents;
	// since the read is committed, the write should be as well. 
	committed.insert(rev->getRev());

	// read_to_val and val_addr_to_reads are empty because the graph is complete already.
	auto exe = Execution(std::move(og), LocalQueueT(), std::move(rev->getRacyRead()), std::move(rev->getRacyWrite()), {}, {}, std::move(committed));
	pushExecution(std::move(exe));

	return true;
}

/**
 * Called when an item is popped from the worklist.
 * Calls the appropriate revisit method based on the type of item.
*/
bool GenMCDriver::restrictAndRevisit(Stamp stamp, WorkSet::ItemT item)
{
	/* First, appropriately restrict the worklist and the graph */	restrictWorklist(stamp);

	lastAdded = item->getPos();
    if (auto *brXmm = llvm::dyn_cast<LBRaceXMMRevisit>(&*item)) {
        std::unique_ptr<LBRaceXMMRevisit> uniqueBrXmm(static_cast<LBRaceXMMRevisit *>(item.release()));
        return lbRaceXMMRevisit(std::move(uniqueBrXmm));
    } 
	else if (auto *frXmm = llvm::dyn_cast<ReadForwardRacyReadTidXMMRevisit>(&*item)) {
		std::unique_ptr<ReadForwardRacyReadTidXMMRevisit> uniqueBrXmm(static_cast<ReadForwardRacyReadTidXMMRevisit *>(item.release()));
		return forwardRacyReadTidXMMRevisit(std::move(uniqueBrXmm));
	}
	else if (auto *hbRev = llvm::dyn_cast<HbPredsXMMRevisit>(&*item)) {
        std::unique_ptr<HbPredsXMMRevisit> uniqueBrXmm(static_cast<HbPredsXMMRevisit *>(item.release()));
		return hbPredsXMMRevisit(std::move(uniqueBrXmm));
	} 
	else if (auto brXmm = llvm::dyn_cast<BackwardXMMRevisit>(&*item)) {
		std::unique_ptr<BackwardXMMRevisit> uniqueBrXmm(static_cast<BackwardXMMRevisit *>(item.release()));
        return backwardXMMRevisit(std::move(uniqueBrXmm));
	}
	else if (llvm::isa<CommittedWriteXMMRevisit>(&*item)) {
		std::unique_ptr<CommittedWriteXMMRevisit> uniqueRev(static_cast<CommittedWriteXMMRevisit *>(item.release()));
        return committedWriteXMMRevisit(std::move(uniqueRev));
	}
	else if (auto *frXmm = llvm::dyn_cast<ReadForwardXMMRevisit>(&*item)) {		
		std::unique_ptr<ReadForwardXMMRevisit> uniqueBrXmm(static_cast<ReadForwardXMMRevisit *>(item.release()));
		getGraph().cutToStamp(stamp);
		getGraph().compressStampsAfter(stamp);
		return forwardXMMRevisit(std::move(uniqueBrXmm));
	}
	else if (auto *fr = llvm::dyn_cast<ForwardRevisit>(&*item)) {
		// g.getKind() == XMM -> !llvm::isa<ReadForwardRevisit>(fr)
		assert(getGraph().getKind() != GraphKind::XMM || !llvm::isa<ReadForwardRevisit>(fr));
		restrictGraph(stamp);
		return forwardRevisit(*fr);
	} else if (auto *br = llvm::dyn_cast<BackwardRevisit>(&*item)) {
		assert(getGraph().getKind() != GraphKind::XMM);
		restrictGraph(stamp);
		return backwardRevisit(*br);
	} else {
        BUG();
        return false;
    }
}

/**
 * Calculate revisits for reads in the thread of the LB racy read.
 * Pushes a XMMRevisitLBRacyReadThread to the worklist.
*/
void GenMCDriver::calcXMMRevisitsLBRacyReadThread()
{
	assert(!execStack.empty());
	auto &g = getGraph();
    auto &currExe = execStack.back();
	assert(currExe.isXMM);
	auto rLab = llvm::dyn_cast<ReadLabel>(g.getEventLabel(currExe.racyRead->getPos()));
	if (!rLab)
		return;
	auto wLab = llvm::dyn_cast<WriteLabel>(g.getEventLabel(currExe.racyWrite->getPos()));
	if (!wLab)
		return;
	assert(rLab);
	assert(wLab);
	
	auto tid = rLab->getThread();
	for (auto index = 0; index < g.getThreadSize(tid); index++) {
		if (index == rLab->getIndex()) // we do not want to revisit the LB racy read, or we would destroy the cycle
			continue;
		if (auto *r = g.getReadLabel({tid, index})) {
			auto stores = getRfsApproximation(r);
			for (auto s : stores) {
				if (r->getRf()->getPos() != s && s.thread != r->getThread() && !areInLoadBufferingRace(r, g.getWriteLabel(s))) {
					auto frXMM = make_unique<ReadForwardRacyReadTidXMMRevisit>(r->getPos(), s, std::make_unique<ReadLabel>(*rLab), std::make_unique<WriteLabel>(*wLab));
					addToWorklist(std::numeric_limits<uint32_t>::max(), std::move(frXMM));
					// Optimization: subsequent ReadForwardRacyReadTidXMMRevisit revisits are not needed 
					// because all options will be explored by Forward revisits
					// so re can return
					return;
				}
			}
		}
	}
}

/**
 * Called when an XMM execution ends.
 * Pushes a XMM HB PREDS reivist to the worklist.
*/
void GenMCDriver::calcXMMRevisitsHbPredecessors()
{
	assert(!execStack.empty());
    auto &g = getGraph();
    auto &currExe = execStack.back();
	assert(currExe.isXMM);
	auto rLab = llvm::dyn_cast<ReadLabel>(g.getEventLabel(currExe.racyRead->getPos()));
	if (!rLab)
		return;
	auto wLab = llvm::dyn_cast<WriteLabel>(g.getEventLabel(currExe.racyWrite->getPos()));
	if (!wLab)
		return;
	assert(rLab);
	assert(wLab);

	// push a revisit for events that are not in the LB cycle po+rf path.
	// it will keep everything except the LB cycle po+rf path and re-execute.
	auto hbRev = std::make_unique<HbPredsXMMRevisit>(rLab->getPos(), wLab->getPos(), std::make_unique<ReadLabel>(*rLab), std::make_unique<WriteLabel>(*wLab));
	addToWorklist(std::numeric_limits<uint32_t>::max(), std::move(hbRev));
}

/**
 * Called when an XMM execution ends.
 * We search in the execution for all load buffering races (areInLoadBufferingRace)
 * For all LB races we create a new LBRaceXMMRevisit, and we push it to the work list
 */
void GenMCDriver::calcXMMRevisitsLbRace()
{
    auto &g = getGraph();
    // iterate through all pair of events and search for special kind of data races:
    //   (1) load-buffering races --- read is porf before write;
    //   (2) consider reads that belong to porf cycle.
    //   TODO: think more about case (2)
    for (auto i = 0u; i < g.getNumThreads(); i++) {
        for (auto j = 0u; j < g.getThreadSize(i); j++) {
            auto *rLab = llvm::dyn_cast<ReadLabel>(g.getEventLabel(Event(i, j)));
            if (!rLab)
                continue;
            for (auto k = 0u; k < g.getNumThreads(); k++) {
                for (auto l = 0u; l < g.getThreadSize(k); l++) {
					auto *eLab = g.getEventLabel(Event(k, l));
					assert(eLab);
                    auto *wLab = llvm::dyn_cast<WriteLabel>(eLab);
                    if (!wLab)
                        continue;
                    if (areInLoadBufferingRace(rLab, wLab)) {
                        auto br = make_unique<LBRaceXMMRevisit>(rLab->getPos(), wLab->getPos(), make_unique<ReadLabel>(*rLab), make_unique<WriteLabel>(*wLab));
						result.lbRacesExplored++;
						// give this revisit maximum priority
                        addToWorklist(std::numeric_limits<uint32_t>::max(), std::move(br));
                    }
                }
            }
        }
    }
}

/**
 * Checks whether g is a duplicate by hashing it.
 * If it's not a duplicate, it is added to the hash set of duplicates.
*/
bool GenMCDriver::isDupElseAdd(const ExecutionGraph &g) {
	// TODO: implement a real hashing function
	if (visitedExecs.find(&g) != visitedExecs.end()) {
		return true;
	} else {
		visitedExecs.insert(g.clone().release());
		return false;
	}
}

/**
 * Calculates the events which should be kept when restricting a graph for a LB race.
 * All events that are not in the po-suffix of racyRead are kept.
*/
View GenMCDriver::calcLBRaceKeptEventsXMM(const ExecutionGraph &g, const ReadLabel *racyRead) const {
    View res;
	for (auto tid = 0; tid < g.getNumThreads(); tid++) {
		if (tid == racyRead->getThread())
			res.setMax(racyRead->getPos());
		else
			res.setMax(g.getLastThreadEvent(tid));
	}
    return res;
}

/**
 * @return true if rLab and wLab are in load buffering race, else false.
 * if rLab reads-from wLab, then they are not considered as a LB race.
*/
bool GenMCDriver::areInLoadBufferingRace(const ReadLabel *rLab, const WriteLabel *wLab) const
{
    const auto &g = getGraph();
	if (!wLab)
		return false;
    if (rLab->getAddr() != wLab->getAddr())
        return false;
	if (rLab->getRf() == wLab)
		return false;
    if (getHbView(wLab).contains(rLab->getPos()) ||
        getHbView(rLab).contains(wLab->getPos()))
        return false;
    const auto &prefix = getPrefixView(wLab);
    if (!prefix.contains(rLab))
        return false;
    // TODO: do we need to check for fences before/after write/read ?
    // for (auto j = rLab->getIndex(); j <= prefix.getMax(rLab->getPos()); j++) {
    //     auto *lab = g.getEventLabel(Event(rLab->getThread(), j));
    //     if (llvm::isa<FenceLabel>(lab) && lab->isAtLeastRelease())
    //         continue;
    // }
    return true;
}

/**
 * Adds all events in g to a hash set. 
 * @param g the graph whose events should be added in the hash set.
 * @return a hash set containing all events in g.
*/
std::unordered_set<Event, EventHasher> GenMCDriver::addAllEventsToSet(const ExecutionGraph &g) const {
	std::unordered_set<Event, EventHasher> result;
	for (auto &lab : labels(g)) 
		result.insert(lab.getPos());
	return result;
}

void GenMCDriver::printGraph(bool printMetadata /* false */, llvm::raw_ostream &s /* = llvm::dbgs() */)
{
	auto &g = getGraph();
	if (g.getKind() == GraphKind::GenMC) {
		s << "GenMC Execution Graph:\n";
	}
	else if (g.getKind() == GraphKind::XMM) {
		s << "XMM Execution Graph:\n";
	}
	else if (g.getKind() == GraphKind::XMM_HB_PREDS) {
		s << "XMM HB PREDS Execution Graph\n";
	}

	LabelPrinter printer([this](const SAddr &saddr){ return getVarName(saddr); },
			     [this](const ReadLabel &lab){
				     return llvm::isa<DskReadLabel>(&lab) ?
					     getDskReadValue(llvm::dyn_cast<DskReadLabel>(&lab)) :
					     getReadValue(&lab);
			     });

	/* Print the graph */
	for (auto i = 0u; i < g.getNumThreads(); i++) {
		auto &thr = EE->getThrById(i);
		s << thr;
		if (getConf()->symmetryReduction) {
			if (auto *bLab = g.getFirstThreadLabel(i)) {
				auto symm = bLab->getSymmetricTid();
				if (symm != -1) s << " symmetric with " << symm;
			}
		}
		s << ":\n";
		for (auto j = 1u; j < g.getThreadSize(i); j++) {
			auto *lab = g.getEventLabel(Event(i, j));
			s << "\t";
			GENMC_DEBUG(
				if (getConf()->colorAccesses)
					s.changeColor(getLabelColor(lab));
			);
			s << printer.toString(*lab);
			GENMC_DEBUG(s.resetColor(););
			// s << " @ " << lab->getStamp();
			GENMC_DEBUG(if (getConf()->printStamps) s << " @ " << lab->getStamp(); );
			if (printMetadata && thr.prefixLOC[j].first && shouldPrintLOC(lab)) {
				executeMDPrint(lab, thr.prefixLOC[j], getConf()->inputFile, s);
			}
			s << "\n";
		}
	}

	/* MO: Print coherence information */
	auto header = false;
	for (auto locIt = g.loc_begin(), locE = g.loc_end(); locIt != locE; ++locIt) {
		/* Skip empty and single-store locations */
		if (g.hasLocMoreThanOneStore(locIt->first)) {
			if (!header) {
				s << "Coherence:\n";
				header = true;
			}
			auto *wLab = &*g.co_begin(locIt->first);
			s << getVarName(wLab->getAddr()) << ": [ ";
			for (const auto &w : stores(g, locIt->first))
				s << w << " ";
			s << "]\n";
		}
	}
	s << "\n";
}

void GenMCDriver::dotPrintGraph(std::ofstream &fout)
{
	llvm::raw_os_ostream ss(fout);

	auto &g = getGraph();
	auto *EE = getEE();
	DotPrinter printer([this](const SAddr &saddr){ return getVarName(saddr); },
			     [this](const ReadLabel &lab){
				     return llvm::isa<DskReadLabel>(&lab) ?
					     getDskReadValue(llvm::dyn_cast<DskReadLabel>(&lab)) :
					     getReadValue(&lab);
			     });

	/* Create a directed graph graph */
	ss << "strict digraph {\n";
	ss << "graph [label=\"" << g.getKind() << "\", fontsize=10, fontcolor=black, labelloc=top]\n";
	/* Specify node shape */
	ss << "node [shape=plaintext]\n";
	/* Left-justify labels for clusters */
	ss << "labeljust=l\n";
	/* Draw straight lines */
	ss << "splines=false\n";

	/* Print all nodes with each thread represented by a cluster */
	for (auto i = 1u; i < g.getNumThreads(); i++) {
		auto &thr = EE->getThrById(i);
		ss << "subgraph cluster_" << thr.id << "{\n";
		ss << "\tlabel=\"" << thr.threadFun->getName().str() << "\"\n";
		for (auto j = 1; j < g.getThreadSize(i) - 1; j++) { // skip THREAD_END label at the end
			auto *lab = g.getEventLabel(Event(i, j));

			ss << "\t\"" << lab->getPos() << "\" [label=<";

			/* First, print the graph label for this node */
			ss << printer.toString(*lab);

			ss << ">";
			if (execStack.back().isXMM) {
				if (Event(i, j) == execStack.back().racyRead->getPos() || Event(i, j) == execStack.back().racyWrite->getPos()) {
					ss << ", fontcolor=red";
				}
				// std::unordered_set<const EventLabel *> visited;
				// std::vector<const EventLabel *> cycleEvents; 
				// auto cycle = calcCycle(g, g.getEventLabel(execStack.back().racyRead->getPos()), visited, cycleEvents);
				// if (cycle && cycle->count(lab) > 0) {
				// 	ss << ", fontcolor=red";
				// }
				if (execStack.back().committedEvents.contains(Event(i, j))) {
					ss << ", shape=box, color=blue";
				}
			}
			ss << "]\n";
		}
		ss << "}\n";
	}

	/* Print relations between events (po U rf) */
	for (auto i = 1u; i < g.getNumThreads(); i++) {
		auto &thr = EE->getThrById(i);
		for (auto j = 0; j < g.getThreadSize(i) - 1; j++) {
			auto *lab = g.getEventLabel(Event(i, j));

			if (auto *rLab = llvm::dyn_cast<ReadLabel>(lab)) {
				/* Do not print RFs from INIT, BOTTOM, and same thread */
				if (llvm::dyn_cast_or_null<WriteLabel>(rLab->getRf()) &&
				    rLab->getRf()->getThread() != lab->getThread()) {
					ss << "\"" << rLab->getRf()->getPos() << "\" -> \""
					   << lab->getPos() << "\"[color=darkgreen, constraint=false, style=dashed]\n";
				}
			}

			/* Print a po-edge, but skip dummy start events for
			 * all threads except for the first one */
			if (!llvm::isa<ThreadStartLabel>(lab) && j < g.getThreadSize(i) - 2) {
				ss << "\"" << lab->getPos() << "\" -> \""
				   << lab->getPos().next() << "\"\n";
			}
		}
	}

	ss << "}\n";
}