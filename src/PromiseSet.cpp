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
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Author: Michalis Kokologiannakis <michalis@mpi-sws.org>
 */

#include "PromiseSet.hpp"

Promise::Promise()
{}

Promise::Promise(std::unique_ptr<WriteLabel> &&lab, std::vector<Event> &&moPrefix)
	: lab(std::move(lab))
	, moPrefix(std::move(moPrefix)) {}

Promise::Promise(const Promise &other)
	: lab(std::unique_ptr<WriteLabel>(other.getLab()->clone()))
	, moPrefix(other.moPrefix)
	, extWrites(other.extWrites)
{}

Promise::Promise(Promise &&other) noexcept
	: lab(std::move(other.lab))
	, moPrefix(std::move(other.moPrefix))
	, extWrites(std::move(other.extWrites))
{}

Promise &Promise::operator=(const Promise &other)
{
	if (this != &other) {
		Promise tmp(other);
		lab.swap(tmp.lab);
		moPrefix.swap(tmp.moPrefix);
		extWrites.swap(tmp.extWrites);
	}
	return *this;
}

Promise &Promise::operator=(Promise &&other) noexcept
{
	if (this != &other) {
		lab = std::move(other.lab);
		moPrefix = std::move(other.moPrefix);
		extWrites = std::move(other.extWrites);
	}
	return *this;
}

Event Promise::getPos() const
{
	return lab->getPos();
}

int Promise::getThread() const
{
	return lab->getThread();
}

const WriteLabel *Promise::getLab() const
{
	return lab.get();
}

const llvm::GenericValue * Promise::getAddr() const
{
	return lab->getAddr();
}

//const std::vector<Event>& Promise::getExtWrites(const llvm::GenericValue *addr) const
//{
//	auto it = extWrites.find(addr);
//	if (it != extWrites.end())
//		return it->second;
//	static std::vector<Event> empty;
//	return empty;
//}

const std::vector<Event> &Promise::getMOPrefix() const
{
	return moPrefix;
}

int Promise::getMOPos() const
{
	if (moPrefix.empty())
		return -1;
	return moPrefix.size() - 1;
}

void Promise::insertIntoMOPrefix(Event w, int offset)
{
	moPrefix.insert(moPrefix.begin() + offset, w);
}

void Promise::addExternalWrite(const WriteLabel *wLab)
{
	extWrites[wLab->getAddr()].push_back(wLab->getPos());
}

bool Promise::isExternalWrite(const WriteLabel *wLab) const
{
	auto it = extWrites.find(wLab->getAddr());
	if (it == extWrites.end())
		return false;
	auto &ws = it->second;
	return std::find(ws.begin(), ws.end(), wLab->getPos()) != ws.end();
}

bool Promise::checkExternalWrites(const std::vector<const WriteLabel *> &ws) const
{
	ExtWrites extWrites_;
	for (auto wLab : ws) {
		extWrites_[wLab->getAddr()].push_back(wLab->getPos());
	}
	return extWrites == extWrites_;
}

/************************************************************
 ** Class Constructors
 ***********************************************************/

PromiseSet::PromiseSet()
	: prmSet()
	, issuePos()
{}

PromiseSet::PromiseSet(Event issuePos, const View &issueView)
	: prmSet()
	, issuePos(issuePos)
	, issueView(issueView)
{}

PromiseSet::PromiseSet(const PromiseSet &other)
	: prmSet(other.prmSet)
	, issuePos(other.issuePos)
	, issueView(other.issueView) {}

PromiseSet::PromiseSet(PromiseSet &&other) noexcept
	: prmSet(std::move(other.prmSet))
	, issuePos(std::move(other.issuePos))
	, issueView(std::move(other.issueView))
{}

PromiseSet& PromiseSet::operator=(const PromiseSet &other)
{
	if (this != &other) {
		PromiseSet tmp(other);
		prmSet.swap(tmp.prmSet);
	}
	return *this;
}

PromiseSet& PromiseSet::operator=(PromiseSet &&other) noexcept
{
	if (this != &other) {
		prmSet = std::move(other.prmSet);
		issuePos = other.issuePos;
	}
	return *this;
}

/************************************************************
 ** Basic getter/setter methods and existential checks
 ***********************************************************/

void PromiseSet::add(Promise &&prm)
{
	BUG_ON(prm.getThread() != getThread());
	prmSet[prm.getAddr()].prms.push_back(std::move(prm));
}

void PromiseSet::certify(const Promise &prm, Event eqw)
{
	const llvm::GenericValue *addr = prm.getAddr();
	auto &entry = prmSet[addr];
	int certPos = entry.certPos();
	BUG_ON(entry.prms.empty());
	BUG_ON(&entry.prms[certPos] != &prm);
	entry.eqws.push_back(eqw);

	if (entry.eqws.size() == entry.prms.size())
		return;

	insertIntoMOPrefix(addr, eqw);
}

const Promise &PromiseSet::getPending(const llvm::GenericValue *addr)
{
	auto& entry = prmSet[addr];
	return entry.prms[entry.certPos()];
}

bool PromiseSet::empty() const
{
	return prmSet.empty();
}

//bool PromiseSet::empty(const llvm::GenericValue *addr) const
//{
//	if (prmSet.count(addr) == 0) {
//		return true;
//	}
//	return prmSet.at(addr).empty();
//}

bool PromiseSet::pending() const
{
	for (const auto& p : prmSet) {
		if (pending(p.first)) {
			return true;
		}
	}
	return false;
}

bool PromiseSet::pending(const llvm::GenericValue *addr) const
{
	auto it = prmSet.find(addr);
	if (it == prmSet.end()) {
		return false;
	}
	return it->second.certPos() < it->second.prms.size();
}

bool PromiseSet::certified() const
{
	return !pending();
}

bool PromiseSet::certified(const llvm::GenericValue *addr) const
{
	return !pending(addr);
}

void PromiseSet::clear()
{
	prmSet.clear();
	issuePos = Event();
	issueView = View();
}

int PromiseSet::getThread() const
{
	return issuePos.thread;
}

Event PromiseSet::getIssuePos() const
{
	return issuePos;
}

int PromiseSet::getIssueIndex() const
{
	return issuePos.index;
}

const View & PromiseSet::getIssuePorfView() const
{
	return issueView;
}

std::vector<const llvm::GenericValue *> PromiseSet::getAddrs() const
{
	std::vector<const llvm::GenericValue *> res;
	for (const auto& entry : prmSet) {
		res.push_back(entry.first);
	}
	return res;
}

std::vector<Event> PromiseSet::getEqualWrites() const
{
	std::vector<Event> res;
	for (const auto& entry : prmSet) {
		auto& eqws = entry.second.eqws;
		res.insert(res.end(), eqws.begin(), eqws.end());
	}
	return res;
}

void PromiseSet::insertIntoMOPrefix(const llvm::GenericValue *addr, Event w)
{
	BUG_ON(certified(addr));
	auto &entry = prmSet[addr];
	int certPos = entry.certPos();

	int moPos = entry.prms[certPos].getMOPos();
	if (moPos < 0)
		return;

	for (int i = certPos; i < entry.prms.size(); ++i) {
		entry.prms[i].insertIntoMOPrefix(w, moPos);
	}
}

bool PromiseSet::isExternalWrite(const WriteLabel *wLab) const
{
	return any_of([&] (const Promise& prm) {
		return prm.isExternalWrite(wLab);
	});
}

/************************************************************
 ** Overloaded Operators
 ***********************************************************/

llvm::raw_ostream& operator<<(llvm::raw_ostream &s, const PromiseSet &prm)
{
	// collect certified and pending promises
	std::vector<Promise> cert;
	std::vector<Promise> pend;
	for (const auto& entry : prm.prmSet) {
		for (size_t i = 0; i < entry.second.certPos(); ++i) {
			cert.push_back(entry.second.prms[i]);
		}
		for (size_t i = entry.second.certPos(); i < entry.second.prms.size(); ++i) {
			pend.push_back(entry.second.prms[i]);
		}
	}

	s << "Promises: { ";
	s << "certified: { ";
	for (const auto &prm: cert) {
		s << *prm.getLab() << " ";
	}
	s << "} ; ";
	s << "pending: { ";
	for (const auto &prm: pend) {
		s << *prm.getLab() << " ";
	}
	s << "} }";
	return s;
}
