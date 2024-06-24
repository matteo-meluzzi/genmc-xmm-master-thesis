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

#ifndef __WKMO_DRIVER_HPP__
#define __WKMO_DRIVER_HPP__

#include "RC11Driver.hpp"

class WKMODriver : public RC11Driver {

public:
	/* Constructor */
	WKMODriver(std::unique_ptr<Config> conf, std::unique_ptr<llvm::Module> mod,
		   std::vector<Library> &granted, std::vector<Library> &toVerify,
		   clock_t start);

	bool inCertificationMode() const;

protected:

//	void changeRf(Event read, Event store) override;

	/*** Schedule related ***/

	bool scheduleNext() override;

	/*** Consistency related ***/

	std::vector<Event> properlyOrderStores(llvm::Interpreter::InstAttr attr,
					       const llvm::Type *typ,
					       const llvm::GenericValue *ptr,
					       llvm::GenericValue &expVal,
					       std::vector<Event> &stores) override;

	bool ensureConsistentRf(const ReadLabel *rLab, std::vector<Event> &rfs) override;

	bool ensureConsistentStore(const WriteLabel *wLab) override;

	bool shouldCheckCons(ProgramPoint p) override;

	bool doPreConsChecks() override;

	/*** Coherence related ***/
	virtual
	std::pair<int, int> getCoherentPlacings(const llvm::GenericValue *addr, Event store, bool isRMW);

	/*** Revisit related ***/

	/* Returns a list of loads from the porf prefix that can be revisited */
	std::vector<Event> getPrefixRevisitable(const WriteLabel *sLab);

	std::vector<Event> getRevisitLoads(const WriteLabel *sLab) override;

	std::unique_ptr<FRevItem> createForwardRevisit(Event r, Event w) override;

	std::unique_ptr<FRevItem> createForwardRevisit(Event r, Event w, PromiseSet&& promises);

	std::unique_ptr<BRevItem> createBackwardRevisit(Event r, Event w) override;

	std::unique_ptr<BRevItem> createBackwardRevisit(const ReadLabel *rLab, const WriteLabel *sLab,
													const VectorClock &prefix, bool pushLoadReorder);

	std::unique_ptr<MOItem> createMORevisit(Event p, int moPos) override;

	bool isDuplicateRevisit(const BRevItem* bri) override;

	/* Pushes additional revisits with promises (upon performing backward revisit)
	 * considering potential load/load reordering,
	 * i.e. by reordering rLab with some subsequent load.
	 */
	void pushBackwardLoadReorderRevisits(const ReadLabel *issLab, const WriteLabel *sLab, const VectorClock &prefix);

	/*** Graph repairing ***/

	bool repairGraph(WorkItem* wi) override;

	/* The following methods are responsible for fixup of po-rf views after a
	 * a change of read-from relation (i.e. a call to `changeRf`).
	 * The fixup is a non-trivial procedure in case of po-rf cyclic execution graph
	 * (in case of RC11-execution with no cycles a call to `fixupPorfViews(reads)`
	 *  is equivalent to call `calcBasicReadViews(read)` for each `read` in `reads`,
	 *  i.e. to simple recalculation of reader's po-rf view).
	 *
	 * Fixes of po-rf views are required when
	 * (1) reads reading from not-yet-certified promises are temporarily set to read from bottom, and
	 * (2) a write that certifies some promise is added to the graph and all reads that were
	 *     reading from that promise are redirected to read from the new write.
	 *
	 * The fixup is a two-phase procedure.
	 *
	 * The first phase is called `relaxPorfViews`.
	 * Views of all events participating into the cycle are relaxed as if there were no cycles.
	 * In more detail, all views of the events in the cycles (and all events reading from some write inside the cycle) are recalculated.
	 * During the recalculation incoming po-rf view of reads reading from the `future`
	 * (i.e. reading from the write whose view contains po-later events) are not taken into account.
	 * The method takes as argument a list of reads whose incoming reads-from edges were changed and
	 * returns a vector of reads that need to be further saturated,
	 * that is for every returned read `r` we have `porf(r) < porf(rf(r))`
	 * (in other words each returned read corresponds to some reads-from edge closing the po-rf cycle).
	 *
	 * The second phase called `saturatePorfViews`.
	 * A DFS-like procedure traverses all the events in the cycle (and events po-rf reachable from the cycle)
	 * and increases the views until the fixpoint is reached (i.e. further updates do not increase the views).
	 *
	 * The `fixupPorfViews` function first calls `relaxPorfViews` to relax views inside the cycle,
	 * obtains the resulting vector of reads that need to be saturated and passes it to `saturatePorfViews`.
	 * It is is invoked after reads reading from a promise are redirected to bottom.
	 *
	 * After all promises are certified and their reads-from are redirected to newly added writes,
	 * the function `saturatePorfViews` is invoked again to fix the views
	 * (note that in this case there is no need to call `relaxPorfViews` since the views can only increase).
	 */

	/* Relaxes and then re-saturates the views of events inside the po-rf cycles */
	void fixupCyclicPorfViews(std::vector<Event> &&redirectedReads);

	/* Relaxes the views of events inside the po-rf cycle.
	 * Starts the exploration from `readsQueue`.
	 */
	std::vector<Event> relaxPorfViews(std::vector<Event> &&readsQueue);

	/* Increases the views of events inside the po-rf cycle.
	 * Starts the exploration from `readsToSaturate`.
	 */
	void saturatePorfViews(std::vector<Event> &&readsToSaturate);

	/*** Promise calculation ***/

	/* Calculates the set of promises that need to be certified
	 * when revisiting issLab with some write event from the given prefix.
	 */
	PromiseSet calcPromises(const ReadLabel *issLab, const VectorClock &prefix) const;

	/* Calculates the set of promises that need to be certified
	 * when revisiting issLab with wLab.
	 */
	PromiseSet calcPromises(const ReadLabel *issLab, const WriteLabel *wLab) const;

	/* Returns true if the promise can be issued via the revisit of rLab by sLab */
	bool canIssuePromise(const Promise &prm, const ReadLabel *rLab, const WriteLabel *sLab);

	/*** Promise certification ***/

	/* Tries to certify the next promise awaiting for the certification.
	 * Takes write label `wLab` as an argument and checks
	 * if it is equivalent to the top promise to the same address.
	 * If so, it removes the promise and returns true.
	 * If there is a promise to the same address,
	 * but it cannot be certified by the write,
	 * returns false and changes its mo-prefix by inserting the write before.
	 * If there are no promises to the address of `wLab`, returns false.
	 */
	bool tryCertifyPromise(const WriteLabel *wLab);

	/* Returns true if promise can be certified by the given write. */
	bool canCertifyPromise(const Promise &prm, const WriteLabel *wLab) const;

	/* Performs some final actions when certification is successfully finished.
	 *
	 * (1) Recalculates porf views after again, because now all reads that
	 *     we reading from the promises are redirected to read from equal writes.
	 * (2) Performs some consistency checks, in order to filter out certified but inconsistent graphs.
	 * (3) Resolves revisits postponed during the certification.
	 */
	void finishCertification();

	/* Resolves delayed revisits by pushing them to the worklist. */
	void resolveDelayedRevisits();

	/* Calculates forward revisits delayed during certification and pushed them to the worklist. */
	void calcDelayedForwardRevisits(const ReadLabel* rLab);

	/* Calculates extra revisits available after certification and pushes them to the worklist.
	 * These revisits can be justified by the load/load reordering of
	 * the revisited load and the load that issued promises.
	 */
	void calcLoadReorderRevisits(ReadLabel *rLab, const EventLabel *certLab);

	/*** Various checks ***/

	/* Checks that read reads from the `future`. */
	bool isFutureRead(const ReadLabel *rLab) const;

	/* Assuming that rLab is porf-before wLab,
	 * returns whether the two events are in an LB race */
	bool areInLBRace(const ReadLabel *rLab, const WriteLabel *wLab);

	/* Checks that two write labels can be announced to be equal
	 * w.r.t. Wkmo model (i.e. they satisfy constraints of `ew` relation).
	 * Note that this function does not perform all the consistency checks
	 * (e.g. it does not check that writes have the same position in `mo`),
	 * and performs only the basic (local) tests.
	 * Namely, it checks that
	 * (1) writes have the same value;
	 * (2) they belong to the same release sequence.
	 */
	bool isEquivalentWrites(const WriteLabel& wLab1, const WriteLabel& wLab2) const;

	/* Returns true if the store is local relative to an event.
	 * The store is local if it is from the same thread as the event
	 * or is porf before event's predecessor. */
	bool isLocalStore(Event event, Event store) const;

	/* Checks whether the read is "justified" to read from the store during certification.
	 * It is the case if store is "local" relative to the read (see `isLocalStore`),
	 * or the store is one of the external stores observed by promises.
	 */
	bool isJustifiedRead(Event store, Event read);

	/*** Utilities ***/

	/* Searches for the next section of a porf cycle in a given thread starting from the given event.
	 * Section of a porf cycle is a sequence of events of a thread participating into the cycle.
	 */
	std::pair<Event, Event> getNextPorfCycleSection(Event e) const;

private:
	/* The set of promises that need to be certified */
	PromiseSet promises;
};

#endif // __WKMO_DRIVER_HPP__
