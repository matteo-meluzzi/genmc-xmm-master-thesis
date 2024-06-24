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

#ifndef __REVISIT_SET_HPP__
#define __REVISIT_SET_HPP__

#include "Event.hpp"
#include "PromiseSet.hpp"

#include <llvm/ADT/Hashing.h>
#include <llvm/Support/raw_ostream.h>
#include <vector>
#include <unordered_map>

/*
 * RevisitSet class - This class represents the revisit set of a particular
 * read in the execution graph
 */
class RevisitSet {

protected:
	struct RevisitItem {
		RevisitItem(const std::vector<Event> &es,
			    const std::vector<std::pair<Event, Event> > &mos,
			    const PromiseSet& prmSet)
			: prefix(es), mos(mos), prmSet(prmSet) {}

		std::vector<Event> prefix;
		std::vector<std::pair<Event, Event> > mos;
		PromiseSet prmSet;
	};

	typedef std::unordered_map<size_t, std::vector<RevisitItem> > RevSet;
	RevSet rev_;

public:
	/* Constructors */
	RevisitSet() : rev_() {}

	/* Iterators */
	typedef RevSet::iterator iterator;
	typedef RevSet::const_iterator const_iterator;
	iterator begin();
	iterator end();
	const_iterator cbegin();
	const_iterator cend();

	/* Basic getter/setters and existential checks */
	void add(const std::vector<Event> &es,
		 const std::vector<std::pair<Event, Event> > &mos,
		 const PromiseSet& prmSet = PromiseSet())
	{
		auto hash = size_t(llvm::hash_combine_range(es.begin(), es.end()));
		rev_[hash].emplace_back(RevisitItem(es, mos, prmSet));
	}

	template <typename PrmCompare = DefaultPromiseComparator>
	bool contains(const std::vector<Event> &es,
		      const std::vector<std::pair<Event, Event> > &mos,
		      const PromiseSet &prmSet = PromiseSet(),
		      PrmCompare&& prmCmp = DefaultPromiseComparator()) const
      	{
      		auto hash = size_t(llvm::hash_combine_range(es.begin(), es.end()));
		if (rev_.count(hash) == 0)
			return false;
		for (auto &p : rev_.at(hash)) {
			if (p.prefix == es && p.mos == mos && p.prmSet.equals(prmSet, prmCmp))
				return true;
		}
		return false;
	}

	/* Overloaded operators */
	friend llvm::raw_ostream& operator<<(llvm::raw_ostream &s, const RevisitSet &rev);
};

#endif /* __REVISIT_SET_HPP__ */
