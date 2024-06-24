/*
 * GenMC -- Generic Model Checking.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Author: Michalis Kokologiannakis <mixaskok@gmail.com>
 */

#ifndef __PROMISE_SET_HPP__
#define __PROMISE_SET_HPP__

#include <vector>
#include <memory>
#include <unordered_map>

#include "EventLabel.hpp"

class Promise {

	typedef std::unordered_map<const llvm::GenericValue *, std::vector<Event>> ExtWrites;

	std::unique_ptr<WriteLabel> lab;
	std::vector<Event> moPrefix;
	ExtWrites extWrites;

public:
	/* Constructors */
	Promise();

	explicit
	Promise(std::unique_ptr<WriteLabel> &&lab, std::vector<Event> &&moPrefix = {});

	Promise(const Promise &other);

	Promise(Promise &&other) noexcept;

	Promise &operator=(const Promise &other);

	Promise &operator=(Promise &&other) noexcept;

	Event getPos() const;

	int getThread() const;

	const WriteLabel* getLab() const;

	const llvm::GenericValue *getAddr() const;

	const std::vector<Event> &getMOPrefix() const;

	int getMOPos() const;

	void insertIntoMOPrefix(Event w, int offset);

	void addExternalWrite(const WriteLabel* wLab);

	bool isExternalWrite(const WriteLabel* wLab) const;

	bool checkExternalWrites(const std::vector<const WriteLabel *> &ws) const;
};

/*
 * PromiseSet class - This class represents the set of promised writes of an ExecutionGraph
 */
class PromiseSet {

	/* The promises are grouped by the memory address they access and
  	 * within each group are totally ordered by their position in po.
  	 * Thus we use a map from addresses to vectors of labels.
  	 *
  	 * Moreover, for each group of promises we store a vector
  	 * of events that were used to certify promises.
  	 * Thus each group of promises is split into two parts,
  	 * left part contains promises that were already certified,
  	 * right part contains pending promises yet to be certified.
  	 * In other words each group of promises forms a sort of queue.
  	 * At the beginning of the queue is the first pending promise, i.e.
  	 * a promise for which there is no equivalent write yet.
  	 */

	struct PrmQueue {
		// promises to a given location
		std::vector<Promise> prms;
		// equivalent writes
		std::vector<Event> eqws;

		size_t certPos() const
		{
			BUG_ON(prms.size() < eqws.size());
			return eqws.size();
		}
	};

	typedef std::unordered_map<const llvm::GenericValue *, PrmQueue> PrmSet;

	PrmSet prmSet;
	Event issuePos;
	View issueView;

public:
	/* Constructors */
	PromiseSet();

	PromiseSet(Event issuePos, const View& issueView);

	PromiseSet(const PromiseSet &other);

	PromiseSet(PromiseSet &&other) noexcept;

	PromiseSet &operator=(const PromiseSet &other);

	PromiseSet &operator=(PromiseSet &&other) noexcept;

	/* Adds the promise to the set */
	void add(Promise &&prm);

	/* Pops the promise from the beginning of the queue of promises to the addr,
	 * and marks it as certified by the write event `eqw` */
	void certify(const Promise &prm, Event eqw);

	/* Get access to the first pending promise to the given address (i.e. next promise to certify) */
	const Promise &getPending(const llvm::GenericValue *addr);

	/* Checks whether the set of promises is empty.
	 * Counts both certified and pending promises. */
	bool empty() const;

	/* Checks if the set of promises to the addr is empty */
	// bool empty(const llvm::GenericValue *addr) const;

	/* Checks whether there are any pending promises */
	bool pending() const;

	/* Checks whether there are any pending promises to the given location */
	bool pending(const llvm::GenericValue *addr) const;

	/* Checks whether all promises have been certified */
	bool certified() const;

	/* Checks whether all promises to the given location have been certified */
	bool certified(const llvm::GenericValue *addr) const;

	/* Removes all the promises, both certified and pending. */
	void clear();

	/* Returns the thread id of the promises
	 * (it's currently assumed that all promises come from the one thread).
	 * If there is no promises return < 0
	 */
	int getThread() const;

	/* Returns position in the graph from which the promises were issued.
	 * In other words, it is the position of the read whose revisit has generated the promises.
	 */
	Event getIssuePos() const;

	/* Returns position in the thread from which the promises were issued. */
	int getIssueIndex() const;

	const View& getIssuePorfView() const;

	/* Returns the vector containing addresses of the promises.
	 * Both certified and pending promises counts.
	 */
	std::vector<const llvm::GenericValue *> getAddrs() const;

	/* Returns the vector containing equal writes,
	 * i.e. writes that were used to certify promises.
	 */
	std::vector<Event> getEqualWrites() const;

	void insertIntoMOPrefix(const llvm::GenericValue *addr, Event w);

	bool isExternalWrite(const WriteLabel *wLab) const;

	/* Applies given function to each promise, both certified and pending.
	 * The function should take `const Promise&` as an argument and return void.
	 */
	template<typename F>
	void apply(F &&f) const
	{
		for (auto &prms: prmSet) {
			for (const auto &prm: prms.second.prms) {
				f(prm);
			}
		}
	}

	/* Applies given function to certified promises only.
	 * Additionally to the promise itself it passes to the function the equal write event.
	 * The function should take `const Promise&` and `Event` as arguments and return void.
	 */
	template<typename F>
	void applyToCertified(F &&f) const
	{
		for (auto &prms: prmSet) {
			auto const &prmQueue = prms.second;
			for (auto i = 0ul; i < prmQueue.certPos(); ++i) {
				f(prmQueue.prms[i], prmQueue.eqws[i]);
			}
		}
	}

	/* Applies given function to pending promises only.
	 * The function should take `const Promise&` as an argument and return void.
	 */
	template<typename F>
	void applyToPending(F &&f) const
	{
		for (auto &prms: prmSet) {
			auto const &prmQueue = prms.second;
			for (auto i = prmQueue.certPos(); i < prmQueue.prms.size(); ++i) {
				f(prmQueue.prms[i]);
			}
		}
	}

	/* Checks if some promise satisfy given predicate.
	 * Checks both certified and pending promises.
	 * The predicate should take `const Promise&` as an argument.
	 */
	template<typename F>
	bool any_of(F &&pred) const
	{
		for (auto &prms: prmSet) {
			for (const auto &prm: prms.second.prms) {
				if (pred(prm)) {
					return true;
				}
			}
		}
		return false;
	}

	/* Checks if all promises satisfy given predicate.
	 * Checks both certified and pending promises.
	 * The predicate should take `const Promise&` as an argument.
	 */
	template<typename F>
	bool all_of(F &&pred) const
	{
		return !any_of([pred](const Promise &prm) {
			return !pred(prm);
		});
	}

	/*
	 * Compares this promise set with other
	 * using provided comparator to compare individual promises.
	 * The comparator should take two `const Promise&` arguments.
	 */
	template<typename Compare>
	bool equals(const PromiseSet &other, Compare &&cmp) const
	{
		for (auto it = prmSet.begin(); it != prmSet.end(); ++it) {
			auto otherIt = other.prmSet.find(it->first);
			if (otherIt == other.prmSet.end()) {
				return false;
			}

			auto& prms = it->second.prms;
			auto& otherPrms = otherIt->second.prms;

			if (prms.size() != otherPrms.size()) {
				return false;
			}

			for (size_t i = 0; i < prms.size(); ++i) {
				if (!cmp(prms[i], otherPrms[i])) {
					return false;
				}
			}
		}
		return true;
	}

	/* Overloaded operators */
	friend llvm::raw_ostream& operator<<(llvm::raw_ostream &s, const PromiseSet& rev);

};

struct DefaultPromiseComparator
{
	bool operator()(const Promise &prm1, const Promise &prm2) const
	{
		return true;
	}
};

#endif /* __PROMISE_SET_HPP__ */

