/*
 * GenMC -- Generic Model Checking.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-3.0.html.
 *
 * Author: Michalis Kokologiannakis <michalis@mpi-sws.org>
 */

#include "config.h"

#include "WKMODriver.hpp"
#include "WBCoherenceCalculator.hpp"
#include "MOCoherenceCalculator.hpp"

WKMODriver::WKMODriver(std::unique_ptr<Config> conf, std::unique_ptr<llvm::Module> mod,
		       std::vector<Library> &granted, std::vector<Library> &toVerify,
		       clock_t start)
	: RC11Driver(std::move(conf), std::move(mod), granted, toVerify, start)
{}

bool WKMODriver::inCertificationMode() const
{
	return promises.pending();
}

// TODO: think again, perhaps we still need to overload `changeRf`
//  and do something about `porf` views, e.g relax them?

//void WKMODriver::changeRf(Event read, Event store)
//{
//	RC11Driver::changeRf(read, store);
//
//	auto &g = getGraph();
//
//	EventLabel *lab = g.getEventLabel(read);
//	BUG_ON(!llvm::isa<ReadLabel>(lab));
//	auto *rLab = static_cast<ReadLabel *>(lab);
//
//	// recalculate justification set
//	auto jfSet = calcBasicJFSet(rLab);
//	rLab->setJFSet(std::move(jfSet));
//
//	return;
//}

bool WKMODriver::repairGraph(WorkItem *wi)
{
	// first call base implementation to restore prefix
	if (!RC11Driver::repairGraph(wi)) {
		return false;
	}

	auto &g = getGraph();
	const EventLabel* lab = g.getEventLabel(wi->getPos());

	promises.clear();

	if (auto* frpi = llvm::dyn_cast<FRevPrmItem>(wi)) {
		promises = frpi->getPromisesRel();
	}
	if (auto* brpi = llvm::dyn_cast<BRevPrmItem>(wi)) {
		promises = brpi->getPromisesRel();
	}
	if (auto* mopi = llvm::dyn_cast<MOPrmItem>(wi)) {
		promises = mopi->getPromisesRel();
	}

	if (!promises.empty()) {
		BUG_ON(wi->getPos().thread != promises.getThread());

		// Make reads reading from the promises read from the bottom temporarily
		promises.applyToCertified([&](const Promise &prm, Event eqw) {
			BUG_ON(!g.checkInGraph(eqw));
			for (auto r: prm.getLab()->getReadersList()) {
				changeRf(r, eqw);
			}
		});
		promises.applyToPending([&](const Promise &prm) {
			for (auto r: prm.getLab()->getReadersList()) {
				changeRf(r, Event::getBottom());
			}
		});

		promises.apply([&](const Promise &prm) {
			auto readers = std::vector<Event>(prm.getLab()->getReadersList());
			fixupCyclicPorfViews(std::move(readers));
		});
	}

	return true;
}

void WKMODriver::fixupCyclicPorfViews(std::vector<Event> &&redirectedReads)
{
	saturatePorfViews(relaxPorfViews(std::move(redirectedReads)));
}

std::vector<Event> WKMODriver::relaxPorfViews(std::vector<Event> &&redirectedReads)
{
	auto &g = getGraph();

	std::vector<Event> stack = std::move(redirectedReads);
	std::vector<Event> readsToSaturate;

	while (!stack.empty()) {
		Event e = stack.back();
		stack.pop_back();

		// `e` is assumed to be a read event;
		// read event cannot be the first event in the thread
		// (first event should have `ThreadCreateLabel`)
		BUG_ON(e == g.getFirstThreadEvent(e.thread));

		// search for the first event not belonging to a cycle
		EventLabel *fstLab = g.getEventLabel(e);
		do {
			fstLab = g.getPreviousLabel(fstLab);
		} while (g.isOnPorfCycle(fstLab) && (fstLab->getPos() != g.getFirstThreadEvent(fstLab->getThread())));

		auto tid = fstLab->getThread();
		auto idx = fstLab->getIndex() + 1;
		View view = fstLab->getPorfView();

		for (int i = idx; i < g.getThreadSize(tid); ++i) {
			++view[tid];
			EventLabel* lab = g.getEventLabel(Event(tid, i));
			if (auto *rLab = llvm::dyn_cast<ReadLabel>(lab)) {
				if (!rLab->getRf().isBottom() && !isFutureRead(rLab)) {
					view.update(g.getPorfBefore(rLab->getRf()));
				}
			}
			if (auto *wLab = llvm::dyn_cast<WriteLabel>(lab)) {
				for (auto& r: wLab->getExternalReadersList()) {
					if (view < g.getPorfBefore(r)) {
						stack.push_back(r);
					} else {
						readsToSaturate.push_back(r);
					}
				}
			}
			lab->setPorfView(View(view));
		}
	}
	return readsToSaturate;
}

void WKMODriver::saturatePorfViews(std::vector<Event> &&readsToSaturate)
{
	auto &g = getGraph();
	auto stack = std::move(readsToSaturate);

	while (!stack.empty()) {
		Event e = stack.back();
		stack.pop_back();

		BUG_ON(!g.checkInGraph(e));

		auto tid = e.thread;
		auto idx = e.index;
		View view = View(g.getPreviousLabel(e)->getPorfView());

		for (int i = idx; i < g.getThreadSize(tid); ++i) {
			view[tid] = std::max(i, view[tid]);
			EventLabel* lab = g.getEventLabel(Event(tid, i));
			if (auto *rLab = llvm::dyn_cast<ReadLabel>(lab)) {
				if (!rLab->getRf().isBottom()) {
					view.update(g.getPorfBefore(rLab->getRf()));
				}
			}
			if (auto *wLab = llvm::dyn_cast<WriteLabel>(lab)) {
				for (auto r: wLab->getExternalReadersList()) {
					if (view > g.getPorfBefore(r)) {
						stack.push_back(r);
					}
				}
			}
			lab->setPorfView(View(view));
		}
	}
}

bool WKMODriver::areInLBRace(const ReadLabel *rLab, const WriteLabel *sLab)
{
	if (rLab->getAddr() != sLab->getAddr())
		return false;

	if (isHbBefore(sLab->getPos(), rLab->getPos()) ||
	    isHbBefore(rLab->getPos(), sLab->getPos()))
		return false;

	auto &g = getGraph();
	auto &porf = g.getPorfBefore(sLab->getPos());
	BUG_ON(!porf.contains(rLab->getPos()));

	if (!isLocalStore(rLab->getPos(), rLab->getRf()))
		return false;

	for (auto j = rLab->getIndex(); j <= porf[rLab->getThread()]; j++) {
		auto *lab = g.getEventLabel(Event(rLab->getThread(), j));
		if (llvm::isa<FenceLabel>(lab) && lab->isAtLeastRelease())
			return false;
	}

	return true;
}

std::vector<Event> WKMODriver::getPrefixRevisitable(const WriteLabel *sLab)
{
	auto &g = getGraph();
	auto &porf = g.getPorfBefore(sLab->getPos());
	std::vector<Event> loads;

	for (auto i = 0u; i < g.getNumThreads(); i++) {
		if (i == sLab->getThread())
			continue;
		for (auto j = 0u; j <= porf[i]; j++) {
			const EventLabel *lab = g.getEventLabel(Event(i, j));
			if (auto *rLab = llvm::dyn_cast<ReadLabel>(lab))
				if (areInLBRace(rLab, sLab))
					loads.push_back(rLab->getPos());
		}
	}
	return loads;
}

std::vector<Event> WKMODriver::getRevisitLoads(const WriteLabel *sLab)
{
	auto& g = getGraph();
	// delay revisits during the certification
	if (inCertificationMode()) {
		return std::vector<Event>{};
	}
	auto ls = g.getRevisitable(sLab);
	auto lsp = getPrefixRevisitable(sLab);
	ls.insert(ls.end(), lsp.begin(), lsp.end());
	return g.getCoherentRevisits(sLab, std::move(ls));
}

std::pair<int, int> WKMODriver::getCoherentPlacings(const llvm::GenericValue *addr, Event store, bool isRMW)
{
	const auto &g = getGraph();
	auto placesRange = RC11Driver::getCoherentPlacings(addr, store, isRMW);

	if (!promises.pending(addr)) {
		return placesRange;
	}

	auto &prm = promises.getPending(addr);
	int moPos = prm.getMOPos();

	if (moPos < 0)
		return std::make_pair(placesRange.first, placesRange.second);

	if (!(moPos >= placesRange.first && moPos <= placesRange.second)) {
		// if the write cannot be inserted at the pending promise position
		// we have a violation of coherence, so we block the exploration
		// TODO: make `blockThreads` method?
		// TODO: block only current thread?
		// TODO: move blocking to some other place?
		for (auto i = 0u; i < getGraph().getNumThreads(); i++)
			getEE()->getThrById(i).block();
		// TODO: what to return in this case?
		return std::make_pair(placesRange.first, placesRange.second);
	}
	return std::make_pair(moPos, moPos);
}

PromiseSet WKMODriver::calcPromises(const ReadLabel *issLab, const VectorClock &prefix) const
{
	const auto &g = getGraph();

	auto rTid = issLab->getThread();
	auto rIdx = issLab->getIndex();
	auto view = g.getViewFromStamp(issLab->getStamp());
	view.update(prefix);
	if (g.isOnPorfCycle(issLab))
		view.update(issLab->getPorfView());
	view.cut(issLab->getPos());

	PromiseSet prmSet(issLab->getPos(), issLab->getPorfView());
	std::vector<const WriteLabel*> extWrites;

	for (auto i = rIdx + 1; i < g.getThreadSize(rTid); ++i) {
		Event e = Event(rTid, i);
		const EventLabel *lab = g.getEventLabel(e);

		if (auto *wLab = llvm::dyn_cast<WriteLabel>(lab)) {
			// calculate the set of reads that read externally from the write
			// and executed before rLab or belong to the po-rf prefix of the sLab
			auto pLab = g.cloneWriteLabelAndKeepReaders(wLab, [&] (Event r) {
				return rTid != r.thread && view.contains(r);
			});
			const std::vector<Event> &extReaders = pLab->getReadersList();
			if (extReaders.empty())
				continue;

			// special check to filter out lock-release writes read by some lock-acquire read
			bool isLockRel = wLab->isAtLeastRelease() &&
				std::any_of(extReaders.begin(), extReaders.end(), [&] (Event r) {
					const EventLabel *lab = g.getEventLabel(r);
					if (auto *lLab = llvm::dyn_cast<CasReadLabel>(lab)) {
						return lLab->isLock();
					}
					return false;
				});
			// we assume that only one dangling lock can exist
			BUG_ON(isLockRel && extReaders.size() > 1);
			if (isLockRel)
				continue;

			auto moPrefix = g.getCoherenceCalculator()->getPrefixRestricted(pLab.get(), view);

			Promise prm(std::move(pLab), std::move(moPrefix));
			for (auto extWLab: extWrites) {
				prm.addExternalWrite(extWLab);
			}
			prmSet.add(std::move(prm));
		}

		if (auto *rLab = llvm::dyn_cast<ReadLabel>(lab)) {
			Event rf = rLab->getRf();
			if (isLocalStore(rLab->getPos(), rf))
				continue;
			auto *extWLab = llvm::dyn_cast<WriteLabel>(g.getEventLabel(rf));
			BUG_ON(!extWLab);
			extWrites.push_back(extWLab);
		}
	}
	return prmSet;
}

PromiseSet WKMODriver::calcPromises(const ReadLabel *issLab, const WriteLabel *wLab) const
{
	return calcPromises(issLab, wLab->getPorfView());
}

std::unique_ptr<FRevItem> WKMODriver::createForwardRevisit(Event r, Event w)
{
	return LLVM_MAKE_UNIQUE<FRevPrmItem>(r, w, PromiseSet(promises));
}

std::unique_ptr<FRevItem> WKMODriver::createForwardRevisit(Event r, Event w, PromiseSet &&promises)
{
	return LLVM_MAKE_UNIQUE<FRevPrmItem>(r, w, std::move(promises));
}

std::unique_ptr<BRevItem> WKMODriver::createBackwardRevisit(Event r, Event w)
{
	auto &g = getGraph();
	const EventLabel *revLab = g.getEventLabel(r);
	const EventLabel *lab = g.getEventLabel(w);
	BUG_ON(!revLab || !lab);
	BUG_ON(!llvm::isa<ReadLabel>(revLab));
	BUG_ON(!llvm::isa<WriteLabel>(lab));
	auto *rLab = static_cast<const ReadLabel *>(revLab);
	auto *sLab = static_cast<const WriteLabel *>(lab);

	return createBackwardRevisit(rLab, sLab, sLab->getPorfView(), true);
}

std::unique_ptr<BRevItem>
WKMODriver::createBackwardRevisit(const ReadLabel *rLab, const WriteLabel *sLab,
								  const VectorClock &prefix, bool pushLoadReorder)
{
	auto &g = getGraph();

	auto writePrefix = g.getPrefixLabelsNotBefore(prefix, rLab);
	auto moPlacings = g.saveCoherenceStatus(writePrefix, rLab);
	auto rPromises = calcPromises(rLab, prefix);

	// skip the revisit if there is some promise which violate our invariants
	bool canIssue = rPromises.all_of([&] (const Promise &prm) {
		return canIssuePromise(prm, rLab, sLab);
	});
	if (!canIssue)
		return nullptr;

	// consider adding additional revisits with promises
	if (pushLoadReorder &&
	    isLocalStore(rLab->getPos(), rLab->getRf()) &&
	    !isLocalStore(rLab->getPos(), sLab->getPos())) {
		pushBackwardLoadReorderRevisits(rLab, sLab, prefix);
	}

	return LLVM_MAKE_UNIQUE<BRevPrmItem>(rLab->getPos(), sLab->getPos(),
		std::move(writePrefix), std::move(moPlacings), std::move(rPromises));
}

void WKMODriver::pushBackwardLoadReorderRevisits(const ReadLabel *issLab, const WriteLabel *sLab, const VectorClock &prefix)
{
	const auto &g = getGraph();

	auto rTid = issLab->getThread();
	auto rIdx = issLab->getIndex();

	// search for the latest promise in the latest porf cycle
	// TODO: stop the search earlier when acquire/release fence/access is found
	auto cycle = getNextPorfCycleSection(issLab->getPos());
	if (!cycle.first.isValid())
		return;
	auto nextCycle = cycle;
	do {
		cycle = nextCycle;
		nextCycle = getNextPorfCycleSection(cycle.second);
	} while (nextCycle.first.isValid());

	const EventLabel *cycleEndLab = g.getEventLabel(cycle.second);

	auto viewPtr = std::unique_ptr<VectorClock>(prefix.clone());
	auto &view = *viewPtr;
	view.update(cycleEndLab->getPorfView());

	auto writePrefix = g.getPrefixLabelsNotBefore(view, issLab);
	auto moPlacings = g.saveCoherenceStatus(writePrefix, issLab);
	auto rPromises = calcPromises(issLab, view);

	// skip the revisit if there is some promise which violate our invariants
	bool canIssue = rPromises.all_of([&] (const Promise &prm) {
		return canIssuePromise(prm, issLab, sLab);
	});
	if (!canIssue)
		return;

	std::unique_ptr<BRevItem> bri = LLVM_MAKE_UNIQUE<BRevPrmItem>(issLab->getPos(), sLab->getPos(),
		std::move(writePrefix), std::move(moPlacings), std::move(rPromises));
	if (!bri || isDuplicateRevisit(bri.get()))
		return;

	addToWorklist(std::move(bri));
}

bool WKMODriver::canIssuePromise(const Promise &prm, const ReadLabel *rLab, const WriteLabel *sLab)
{
	auto &g = getGraph();
	auto *cc = g.getCoherenceCalculator();

	// Check that the promise is relaxed write
	// TODO: discuss it with Viktor and Soham at some point.
	if (!prm.getLab()->isRelaxed()) {
		return false;
	}

	// Check that there are no acquire fences or accesses
	// to the same location as the revisiting read
	// between the read we are revisiting and the promise.
	// As a byproduct it also checks that the read being revisited is relaxed read.
	Event acq = g.getLastThreadAcquireAtLoc(prm.getPos(), rLab->getAddr());
	if (rLab->getIndex() <= acq.index)
		return false;

	// Check that the msg view of the promise does not contain the revisited read,
	// otherwise it would imply there is some release write
	// or fence between the read and the promise.
	if (prm.getLab()->getMsgView().contains(rLab->getPos())) {
		return false;
	}

	// TODO: make two checks above about acquire/release more uniform,
	//  e.g. add something like `acquireView`?

	// Check that the promise is not `mo` earlier than the write we are using for revisit,
	// otherwise we would not be able to find an equivalent write with the same `mo` position.
	// Also checks for coherence or atomicity violations on the road.
	if (prm.getAddr() == sLab->getAddr()) {

		if (auto *moC = llvm::dyn_cast<MOCoherenceCalculator>(cc)) {
			auto prefix = moC->getMOBefore(sLab->getAddr(), sLab->getPos());
			return std::find(prefix.begin(), prefix.end(), prm.getPos()) == prefix.end();
		}

		if (auto *wbC = llvm::dyn_cast<WBCoherenceCalculator>(cc)) {
			auto wb = wbC->calcWb(prm.getAddr());
			wb.transClosure();
			return wb.isIrreflexive() && !wb(prm.getPos(), sLab->getPos());
		}
	}
	return true;
}

std::unique_ptr<MOItem> WKMODriver::createMORevisit(Event p, int moPos)
{
	return LLVM_MAKE_UNIQUE<MOPrmItem>(p, moPos, PromiseSet(promises));
}

bool WKMODriver::isDuplicateRevisit(const BRevItem *bri)
{
	// TODO: get rid of copy-paste from `GenMCDriver`

	auto& g = getGraph();
	const EventLabel *rLab = g.getEventLabel(bri->getPos());
	const EventLabel *sLab = g.getEventLabel(bri->getRev());
	BUG_ON(!rLab || !sLab);

	auto writePrefixPos = g.extractRfs(bri->getPrefixNoRel());
	writePrefixPos.insert(writePrefixPos.begin(), sLab->getPos());

	const auto& moPlacings = bri->getMOPlacingsNoRel();

	auto *cycbri = llvm::dyn_cast<BRevPrmItem>(bri);
	BUG_ON(!cycbri);

	const auto& prms = cycbri->getPromisesNoRel();

	auto prmCmp = [this] (const Promise &prm1, const Promise &prm2) {
		return isEquivalentWrites(*prm1.getLab(), *prm2.getLab()) &&
		       prm1.getMOPrefix() == prm2.getMOPrefix();
	};

	auto& revisitSet = getRevisitSet(rLab->getStamp());

	if (!revisitSet.contains(writePrefixPos, moPlacings, prms, prmCmp)) {
		revisitSet.add(writePrefixPos, moPlacings, prms);
		return false;
	}
	return true;
}

bool WKMODriver::scheduleNext()
{
	// TODO: remove copy-paste from `GenMCDriver`
	if (isMoot())
		return false;

	const auto &g = getGraph();
	auto *EE = getEE();

	/* Check if there are outstanding promises */
	// TODO: WKMODriver --- push to threadPrios (and check it's empty)
	if (inCertificationMode()) {
		auto tid = promises.getThread();
		BUG_ON(tid < 0);
		auto &thr = EE->getThrById(tid);
		if (!thr.ECStack.empty() && !thr.isBlocked &&
			!llvm::isa<ThreadFinishLabel>(g.getLastThreadLabel(tid))) {
			EE->currentThread = tid;

			return true;
		} else {
			/* if there are outstanding promises but
			 * the thread is blocked or stuck we are done */

			return false;
		}
	}
	return RC11Driver::scheduleNext();
}

bool WKMODriver::shouldCheckCons(ProgramPoint p)
{
	// during certification do not check consistency at individual steps,
	// but check it at other points (e.g. error or end of execution)
	if (inCertificationMode()) {
		return (p < ProgramPoint::step);
	}
	return RC11Driver::shouldCheckCons(p);
}

bool WKMODriver::doPreConsChecks()
{
	/* We consider an execution inconsistent, if there are pending promises left.
	 * Also if we encounter an error in the middle of the certification process (for po-rf cycle),
	 * abort the certification and consider it as failed.
	 * TODO: discuss semantics of assert/error during the certification with Viktor.
	 */
	return !promises.pending();
}

std::vector<Event> WKMODriver::properlyOrderStores(llvm::Interpreter::InstAttr attr,
						   const llvm::Type *typ,
						   const llvm::GenericValue *ptr,
						   llvm::GenericValue &expVal,
						   std::vector<Event> &stores)
{
	if (inCertificationMode()) {
		auto remIt = std::remove_if(stores.begin(), stores.end(), [&] (Event store) {
			return !isJustifiedRead(store, getEE()->getCurrentPosition());
		});
		stores.erase(remIt, stores.end());
		BUG_ON(stores.empty());
	}

	return RC11Driver::properlyOrderStores(attr, typ, ptr, expVal, stores);
}

bool WKMODriver::ensureConsistentRf(const ReadLabel *rLab, std::vector<Event> &rfs)
{
	return RC11Driver::ensureConsistentRf(rLab, rfs);
}

bool WKMODriver::ensureConsistentStore(const WriteLabel *wLab)
{
	if (inCertificationMode()) {
		tryCertifyPromise(wLab);
		if (promises.certified()) {
			finishCertification();
			return true;
		}
	}
	return RC11Driver::ensureConsistentStore(wLab);
}

bool WKMODriver::tryCertifyPromise(const WriteLabel *wLab)
{
	auto &g = getGraph();

	auto wTid = wLab->getThread();
	auto wAddr = wLab->getAddr();
	if (!promises.pending(wAddr)) {
		return false;
	}

	const Promise &prm = promises.getPending(wAddr);
	BUG_ON(wTid != prm.getThread());

	if (!canCertifyPromise(prm, wLab)) {
		promises.insertIntoMOPrefix(wAddr, wLab->getPos());
		return false;
	}

	// fix external readers of the promise;
	// we assume that events from other threads,
	// i.e. not the thread which promises we certify,
	// do not change their position and so it's fine
	// to access them by their (tid, n) indices.
	for (auto &r : prm.getLab()->getReadersList()) {
		g.changeRf(r, wLab->getPos());
	}
	promises.certify(prm, wLab->getPos());
	return true;
}

bool WKMODriver::canCertifyPromise(const Promise &prm, const WriteLabel *wLab) const
{
	const auto &g = getGraph();

	if (!isEquivalentWrites(*wLab, *prm.getLab())) {
		return false;
	}

	const EventLabel *issLab = g.getEventLabel(promises.getIssuePos());
	BUG_ON(!llvm::isa<ReadLabel>(issLab));
	auto *issRLab = static_cast<const ReadLabel*>(issLab);

	// Check that there are no acquire/release fences or accesses
	// to the promise's location between the read we are revisiting and the promise.
	// Currently, we perform this check at the point when we try to pick an equal write for some promise.
	// It would be more efficient to just abort certification whenever we encounter
	// (1) an acquire/release fence;
	// (2) acquire read to the location of the read that issued the promises;
	// (3) release write to the location for which there are pending promises;
	// (4) RMW reading from a release sequence unseen by the promises to the same location.
	// However, the current implementation is more concise and straightforward and so for now we keep it.
	// We will implement earlier aborts later if that would be necessary for the performance considerations.

	Event acq = g.getLastThreadAcquireAtLoc(wLab->getPos(), issRLab->getAddr());
	if (issRLab->getIndex() <= acq.index)
		return false;

	if (wLab->getMsgView() != prm.getLab()->getMsgView()) {
		return false;
	}

	// TODO: make two checks above about acquire/release more uniform,
	//  e.g. add something like `acquireView`?

	// Check that certification write is not hb-after any of the reads that should read from it.
	// Reading from hb-later write would obviously violate coherence.
	// Ideally, we should detect this problem earlier and abort certification at that point.
	// For now, we implement this naive terribly inefficient solution.
	// TODO: fix it (abort certification earlier)!!!
	for (auto &r : prm.getLab()->getReadersList()) {
		if (wLab->getHbView().contains(r)) {
			return false;
		}
	}

	auto issTid = issRLab->getThread();
	auto issIdx = issRLab->getIndex();

	// Check what writes are read "non-locally" and their order.
	// This check should prevent various bait-and-switch types of behavior.
	std::vector<const WriteLabel*> extWrites;
	for (auto i = issIdx + 1; i < wLab->getIndex(); ++i) {
		const EventLabel *lab = g.getEventLabel(Event(issTid, i));
		if (auto *rLab = llvm::dyn_cast<ReadLabel>(lab)) {
			Event rf = rLab->getRf();
			if (isLocalStore(rLab->getPos(), rf))
				continue;
			auto *extWLab = llvm::dyn_cast<WriteLabel>(g.getEventLabel(rf));
			BUG_ON(!extWLab);
			extWrites.push_back(extWLab);
		}
	}
	return prm.checkExternalWrites(extWrites);
}

void WKMODriver::finishCertification()
{
	BUG_ON(promises.empty() || !promises.certified());

	promises.apply([this] (const Promise& prm) {
		auto readers = prm.getLab()->getReadersList();
		saturatePorfViews(std::move(readers));
	});

	if (!isConsistent(false)) {
		for (auto i = 0u; i < getGraph().getNumThreads(); i++)
			getEE()->getThrById(i).block();
		return;
	}

	resolveDelayedRevisits();
	promises.clear();

	return;
}

void WKMODriver::resolveDelayedRevisits()
{
	BUG_ON(!promises.certified());

	auto& g = getGraph();
	Event issuePos = promises.getIssuePos();

	auto equalWrites = promises.getEqualWrites();
	std::sort(equalWrites.begin(), equalWrites.end());

	const EventLabel *certLab = g.getEventLabel(equalWrites.back());

	BUG_ON(equalWrites.empty());
	BUG_ON(equalWrites.front().index <= promises.getIssueIndex());
	BUG_ON(certLab->getIndex() != g.getLastThreadLabel(issuePos.thread)->getIndex());

	// We iterate through all events in the thread between
	// the position where promises were issued, i.e. position of the read that was revisited,
	// and the position of the last event, i.e position where certification has finished successfully.
	// We search for write events, that were not used to certify promises,
	// and generate backward revisits for them.
	// We also generate non-local forward revisits for read events.

	auto eqwIt = equalWrites.begin();

	for (int i = issuePos.index + 1; i <= certLab->getIndex(); ++i) {
		const EventLabel *lab = g.getEventLabel(Event(issuePos.thread, i));
		if (i == eqwIt->index) {
			++eqwIt;
			continue;
		}
		if (auto *wLab = llvm::dyn_cast<WriteLabel>(lab)) {
			calcRevisits(wLab);
		}
		if (auto *rLab = llvm::dyn_cast<ReadLabel>(lab)) {
			calcDelayedForwardRevisits(rLab);
		}
	}

	// We generate additional revisits for the local reads in the thread under certification.
	// For each such read we generate revisit with non-local store and
	// the same set of promises as were currently certified.

	// TODO: check for acquire/release fences in-between,
	//   - start the search only from the latest fence
	for (int i = 0; i < issuePos.index; ++i) {
		EventLabel *lab = g.getEventLabel(Event(issuePos.thread, i));
		if (auto *rLab = llvm::dyn_cast<ReadLabel>(lab)) {
			calcLoadReorderRevisits(rLab, certLab);
		}
	}

	// Also we need to generate revisits for the write event that was used to generate current cyclic execution.
	// We only need to push non-cyclic revisits for the revisitable reads.
	// Note that we have to consider `po+rf` prefix of the write event
	// as it was before we have modified the graph.

	const EventLabel *issueLab = g.getEventLabel(issuePos);
	BUG_ON(!issueLab || !llvm::isa<ReadLabel>(issueLab));
	const ReadLabel *issueRLab = static_cast<const ReadLabel *>(issueLab);

	const EventLabel *revLab = g.getEventLabel(issueRLab->getRf());
	BUG_ON(!revLab || !llvm::isa<WriteLabel>(revLab));
	auto *revWLab = static_cast<const WriteLabel *>(revLab);

	View issueView(promises.getIssuePorfView());
	issueView.update(revWLab->getPorfView());
	auto revLoads = g.getRevisitable(revWLab->getAddr(), issueView);
	calcRevisits(revWLab, std::move(revLoads));
//	calcRevisits(revWLab);
}

void WKMODriver::calcDelayedForwardRevisits(const ReadLabel *rLab)
{
	const auto& g = getGraph();

	// TODO: get rid of copypaste from GenMCDriver::visitLoad !!!
	auto stores = getStoresToLoc(rLab->getAddr());
	auto remIt = std::remove_if(stores.begin(), stores.end(), [&] (Event store) {
		return isJustifiedRead(store, getEE()->getCurrentPosition());
	});
	stores.erase(remIt, stores.end());

	auto validStores = GenMCDriver::properlyOrderStores(rLab, stores);
	for (auto it = validStores.begin(); it != validStores.end(); ++it) {
		auto *wLab = llvm::dyn_cast<WriteLabel>(g.getEventLabel(*it));
		BUG_ON(!wLab);

		addToWorklist(createForwardRevisit(rLab->getPos(), *it, calcPromises(rLab, wLab)));
	}
}

void WKMODriver::calcLoadReorderRevisits(ReadLabel *rLab, const EventLabel *certLab)
{
	const auto& g = getGraph();

 	// skip non-local reads
	if (!isLocalStore(rLab->getPos(), rLab->getRf()))
		return;

	// TODO: get rid of copypaste from GenMCDriver::visitLoad !!!
	auto stores = getStoresToLoc(rLab->getAddr());
	auto validStores = GenMCDriver::properlyOrderStores(rLab, stores);
	for (auto it = validStores.begin(); it != validStores.end(); ++it) {
		if (isLocalStore(rLab->getPos(), *it))
			continue;
		auto *wLab = llvm::dyn_cast<WriteLabel>(g.getEventLabel(*it));
		BUG_ON(!wLab);

		auto view = wLab->getPorfView();
		view.update(certLab->getPorfView());

		std::unique_ptr<BRevItem> bri = createBackwardRevisit(rLab, wLab, view, false);
		if (!bri || isDuplicateRevisit(bri.get()))
			continue;

		addToWorklist(std::move(bri));
	}

	// also make the read revisitable again so that later backward revisits can see it
	rLab->setRevisitStatus(true);
}

bool WKMODriver::isFutureRead(const ReadLabel *rLab) const
{
	const auto &g = getGraph();
	Event w = rLab->getRf();
	return g.getPorfBefore(w)[rLab->getThread()] > rLab->getIndex();
}

bool WKMODriver::isEquivalentWrites(const WriteLabel &wLab1, const WriteLabel &wLab2) const
{
	return getEE()->compareValues(wLab1.getType(), wLab1.getVal(), wLab2.getVal());
}

bool WKMODriver::isLocalStore(Event event, Event store) const
{
	const auto &g = getGraph();

	BUG_ON(store.isBottom());
	BUG_ON(event == g.getFirstThreadEvent(event.thread));

	if (store.isInitializer())
		return true;
	// TODO: this check could be subsumed by the next one?
	if (store.thread == event.thread)
		return true;
	if (g.getPreviousLabel(event)->getHbView().contains(store))
		return true;

	const EventLabel *lab = g.getEventLabel(store);
	BUG_ON(!llvm::isa<WriteLabel>(lab));
	auto *wLab = static_cast<const WriteLabel*>(lab);

	for (auto r: wLab->getReadersList()) {
		if (g.getPreviousLabel(event)->getHbView().contains(r))
			return true;
	}

	return false;
}

bool WKMODriver::isJustifiedRead(Event store, Event read)
{
	const auto &g = getGraph();

	if (isLocalStore(read, store))
		return true;

	const EventLabel *lab = g.getEventLabel(store);
	BUG_ON(!llvm::isa<WriteLabel>(lab));
	auto *wLab = static_cast<const WriteLabel*>(lab);

	if (promises.isExternalWrite(wLab))
		return true;

	return false;
}

std::pair<Event, Event> WKMODriver::getNextPorfCycleSection(Event e) const
{
	const auto &g = getGraph();

	// search for the first event not belonging to a cycle
	const EventLabel *lab = g.getEventLabel(e);
	while (!g.isOnPorfCycle(lab) && e < g.getLastThreadEvent(e.thread)) {
		e.index++;
		lab = g.getEventLabel(e);
	}
	if (e == g.getLastThreadEvent(e.thread))
		return std::make_pair(Event(), Event());
	// beginning of a cycle
	Event cycleBegin = e;

	while (g.isOnPorfCycle(lab)) {
		BUG_ON(e == g.getLastThreadEvent(e.thread));
		e.index++;
		lab = g.getEventLabel(e);
	}
	// end of a cycle
	Event cycleEnd = e;

	return std::make_pair(cycleBegin, cycleEnd);
}