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

#ifndef __REVISIT_HPP__
#define __REVISIT_HPP__

#include "EventLabel.hpp"
#include "ExecutionGraph.hpp"
#include <map>
#include <unordered_map>

using tid_t = unsigned int;
using val_t = uint64_t;
using ValAddrTidToReadsMap = std::map<std::tuple<SAddr, val_t, tid_t>, std::unordered_set<Event, EventHasher>>;
using ReadToValMap = std::unordered_map<Event, val_t, EventHasher>;

class ReadRevisit;

/*
 * Revisit class (abstract) - Represents a revisit operation
 */
class Revisit {

public:
	/* LLVM-style RTTI discriminator */
	enum Kind {
		RV_FRev,
		RV_FRevRead,
		RV_FRevMO,
		RV_FRevOpt,
		RV_FRevLast,
        RV_FRevXMM,
		RV_FRevRacyReadTidXMM,
        RV_BRev,
		RV_BRevHelper,
		RV_BRevXMM,
		RV_BRevLast,
		RV_Rev_HB_PREDS_XMM,
		RV_LBRaceXMM,
		RV_CommittedWriteXMM
	};

protected:
	/* Constructors */
	Revisit() = delete;
	Revisit(Kind k, Event p) : kind(k), pos(p) {}

public:
	/* Returns the kind of this item */
	Kind getKind() const { return kind; }

	/* Returns the event for which we are exploring an alternative exploration option */
	Event getPos() const { return pos; }

	static bool classofKind(Kind K) { return true; }
	static ReadRevisit *castToReadRevisit(const Revisit *);
	static Revisit *castFromReadRevisit(const ReadRevisit *);

	/* Destructor and printing facilities */
	virtual ~Revisit() {}
	friend llvm::raw_ostream& operator<<(llvm::raw_ostream& rhs, const Revisit &item);

private:
	Kind kind;
	Event pos;
};

llvm::raw_ostream& operator<<(llvm::raw_ostream& rhs, const Revisit::Kind k);


/* Multiple hierarchy for read revisits */
class ReadRevisit {

protected:
	ReadRevisit(Revisit::Kind k, Event rev)
		: revisitKind(k), rev(rev) {}

public:
	Event getRev() const { return rev; }

	Revisit::Kind getRevisitKind() const {
		return revisitKind;
	}

	static bool classof(const Revisit *r) {
		return r->getKind() == Revisit::RV_FRevRead ||
		       (r->getKind() >= Revisit::RV_BRev && r->getKind() <= Revisit::RV_BRevLast) || r->getKind() == Revisit::RV_FRevXMM;
	}

private:
	Revisit::Kind revisitKind;

	/* The store revisiting the read */
	Event rev;
};

/* Multiple hierarchy for re-execution revisits */
class XMMRevisit {
public:
    XMMRevisit(std::unique_ptr<ReadLabel> read, std::unique_ptr<WriteLabel> write)
        : racyRead(std::move(read)),
          racyWrite(std::move(write))
    {}

    const std::unique_ptr<ReadLabel> &getRacyRead() const {
        return racyRead;
    }

    std::unique_ptr<ReadLabel> &getRacyRead() {
        return racyRead;
    }

    const std::unique_ptr<WriteLabel> &getRacyWrite() const {
        return racyWrite;
    }

    std::unique_ptr<WriteLabel> &getRacyWrite() {
        return racyWrite;
    }

private:
    std::unique_ptr<ReadLabel> racyRead;
    std::unique_ptr<WriteLabel> racyWrite;
};

/*
 * ForwardRevisit class (abstract) - Represents a forward revisit
 */
class ForwardRevisit : public Revisit {

protected:
	ForwardRevisit() = delete;
	ForwardRevisit(Kind k, Event p) : Revisit(k, p) {}

public:
	static bool classof(const Revisit *item) {
		return item->getKind() >= RV_FRev && item->getKind() <= RV_FRevLast;
	}
};


/*
 * ReadForwardRevisit class - Forward revisit a read
 */
class ReadForwardRevisit : public ForwardRevisit, public ReadRevisit {

protected:

    ReadForwardRevisit(Kind kind, Event p, Event r, bool m = false)
        : ForwardRevisit(kind, p),maximal(m),
          ReadRevisit(kind, r)
    {}

public:
	/* Constructors */
	ReadForwardRevisit() = delete;
	ReadForwardRevisit(Event p, Event r, bool m = false)
		: ReadForwardRevisit(RV_FRevRead, p, r, m)
    {}

	bool isMaximal() const { return maximal; }

	static bool classof(const Revisit *item) {
		return (item->getKind() == RV_FRevRead) || (item->getKind() == RV_FRevXMM);
	}
	static ReadRevisit *castToReadRevisit(const ReadForwardRevisit *r) {
		return static_cast<ReadRevisit *>(const_cast<ReadForwardRevisit*>(r));
	}
	static ReadForwardRevisit *castFromReadRevisit(const ReadRevisit *r) {
		return static_cast<ReadForwardRevisit *>(const_cast<ReadRevisit*>(r));
	}

private:
	bool maximal;
};


/*
 * WriteForwardRevisit class - Represents an alternative MO position for a store
 * (Used by drivers that track MO only)
 */
class WriteForwardRevisit : public ForwardRevisit {

protected:
	WriteForwardRevisit(Kind k, Event p, Event moSucc)
		: ForwardRevisit(k, p), moSucc(moSucc) {}

public:
	WriteForwardRevisit(Event p, Event moSucc)
		: WriteForwardRevisit(RV_FRevMO, p, moSucc) {}

	/* Returns the new MO successor of the event for which
	 * we are exploring alternative exploration options */
	Event getSucc() const { return moSucc; }

	static bool classof(const Revisit *item) {
		return item->getKind() == RV_FRevMO;
	}

private:
	Event moSucc;
};

/*
 * OptionalForwardRevisit class - Represents the revisit of an optional block
 */
class OptionalForwardRevisit : public ForwardRevisit {

public:
	OptionalForwardRevisit(Event p) : ForwardRevisit(RV_FRevOpt, p) {}

	static bool classof(const Revisit *item) {
		return item->getKind() == RV_FRevOpt;
	}
};

class ReadForwardXMMRevisit : public ReadForwardRevisit, public XMMRevisit {
public:
    /* Constructors */
    ReadForwardXMMRevisit() = delete;
    ReadForwardXMMRevisit(Event p, Event r, std::unique_ptr<ReadLabel> read, std::unique_ptr<WriteLabel> write, 
		ValAddrTidToReadsMap val_addr_to_reads_in_graph, ReadToValMap read_in_graph_to_val,
		std::unordered_set<Event, EventHasher> committedEvents)
        : ReadForwardRevisit(RV_FRevXMM, p, r, false),
          XMMRevisit(std::move(read), std::move(write)),
		  val_addr_to_reads_in_graph(std::move(val_addr_to_reads_in_graph)),
		  read_in_graph_to_val(std::move(read_in_graph_to_val)),
		  committedEvents(std::move(committedEvents))
    {}

	ValAddrTidToReadsMap val_addr_to_reads_in_graph;
	ReadToValMap read_in_graph_to_val;
	std::unordered_set<Event, EventHasher> committedEvents;
    
	static bool classof(const Revisit *item) {
        return item->getKind() == RV_FRevXMM;
    }
    static ReadRevisit *castToReadRevisit(const ReadForwardXMMRevisit *r) {
        return static_cast<ReadRevisit *>(const_cast<ReadForwardXMMRevisit*>(r));
    }
    static ReadForwardXMMRevisit *castFromReadRevisit(const ReadRevisit *r) {
        return static_cast<ReadForwardXMMRevisit *>(const_cast<ReadRevisit*>(r));
    }
};

/*
 * BackwardRevisit class - Represents a backward revisit
 */
class BackwardRevisit : public Revisit, public ReadRevisit {

protected:
	BackwardRevisit(Kind k, Event p, Event r, std::unique_ptr<VectorClock> view)
		: Revisit(k, p),
		  view(std::move(view)),
		  ReadRevisit(k, r) {}

public:
	BackwardRevisit(Event p, Event r, std::unique_ptr<VectorClock> view)
		: BackwardRevisit(RV_BRev, p, r, std::move(view)) {}
	BackwardRevisit(const ReadLabel *rLab, const WriteLabel *wLab, std::unique_ptr<VectorClock> view)
		: BackwardRevisit(rLab->getPos(), wLab->getPos(), std::move(view)) {}

	/* Returns (releases) the prefix of the revisiting event */
	std::unique_ptr<VectorClock> getViewRel() {
		return std::move(view);
	}

	/* Returns (but does not release) the prefix of the revisiting event */
	const std::unique_ptr<VectorClock> &getViewNoRel() const {
		return view;
	}

	static bool classof(const Revisit *item) {
		return item->getKind() >= RV_BRev && item->getKind() <= RV_BRevLast;
	}
	static ReadRevisit *castToReadRevisit(const BackwardRevisit *r) {
		return static_cast<ReadRevisit *>(const_cast<BackwardRevisit*>(r));
	}
	static BackwardRevisit *castFromReadRevisit(const ReadRevisit *r) {
		return static_cast<BackwardRevisit *>(const_cast<ReadRevisit*>(r));
	}

private:
	std::unique_ptr<VectorClock> view;
};

class BackwardXMMRevisit : public BackwardRevisit, public XMMRevisit {
public:
	BackwardXMMRevisit(Event p, Event r, std::unique_ptr<VectorClock> view,
			std::unique_ptr<ReadLabel> read, std::unique_ptr<WriteLabel> write,
			ValAddrTidToReadsMap val_addr_to_reads_in_graph, ReadToValMap read_in_graph_to_val,
			std::unordered_set<Event, EventHasher> committedEvents)
		: BackwardRevisit(RV_BRevXMM, p, r, std::move(view)),
		  XMMRevisit(std::move(read), std::move(write)),
		  val_addr_to_reads_in_graph(std::move(val_addr_to_reads_in_graph)),
		  read_in_graph_to_val(std::move(read_in_graph_to_val)),
		  committedEvents(std::move(committedEvents))
		{}
	
	ValAddrTidToReadsMap val_addr_to_reads_in_graph;
	ReadToValMap read_in_graph_to_val;
	std::unordered_set<Event, EventHasher> committedEvents;

	static bool classof(const Revisit *item) {
		return item->getKind() >= RV_BRevXMM && item->getKind() <= RV_BRevLast;
	}
    static ReadRevisit *castToReadRevisit(const BackwardXMMRevisit *r) {
        return static_cast<ReadRevisit *>(const_cast<BackwardXMMRevisit*>(r));
    }
    static BackwardXMMRevisit *castFromReadRevisit(const ReadRevisit *r) {
        return static_cast<BackwardXMMRevisit *>(const_cast<ReadRevisit*>(r));
    }
};


/*
 * BackwardRevisitHELPER class - Represents an optimized BR performed by Helper
 */
class BackwardRevisitHELPER : public BackwardRevisit {

public:
	BackwardRevisitHELPER(Event p, Event r, std::unique_ptr<VectorClock> view, Event m)
		: BackwardRevisit(RV_BRevHelper, p, r, std::move(view)), mid(m) {}
	BackwardRevisitHELPER(const ReadLabel *rLab, const WriteLabel *wLab, std::unique_ptr<VectorClock> view,
			      const WriteLabel *mLab)
		: BackwardRevisitHELPER(rLab->getPos(), wLab->getPos(), std::move(view),
					mLab->getPos()) {}

	/* Returns the intermediate write participating in the revisit */
	Event getMid() const { return mid; }

	static bool classof(const Revisit *item) {
		return item->getKind() == RV_BRevHelper;
	}
	static ReadRevisit *castToReadRevisit(const BackwardRevisitHELPER *r) {
		return static_cast<ReadRevisit *>(const_cast<BackwardRevisitHELPER*>(r));
	}
	static BackwardRevisitHELPER *castFromReadRevisit(const ReadRevisit *r) {
		return static_cast<BackwardRevisitHELPER *>(const_cast<ReadRevisit*>(r));
	}

private:
	Event mid;
};

class LBRaceXMMRevisit : public Revisit, public ReadRevisit, public XMMRevisit {
public:
    /* Constructors */
    LBRaceXMMRevisit() = delete;
    LBRaceXMMRevisit(Event p, Event r,
            std::unique_ptr<ReadLabel> read, std::unique_ptr<WriteLabel> write)
		: Revisit(RV_LBRaceXMM, p),
		  ReadRevisit(RV_LBRaceXMM, r),
		  XMMRevisit(std::move(read), std::move(write))
    {}

    static bool classof(const Revisit *item) {
        return item->getKind() == RV_LBRaceXMM;
    }
};

class HbPredsXMMRevisit : public Revisit, public ReadRevisit, public XMMRevisit {
public:
	HbPredsXMMRevisit() = delete;
    HbPredsXMMRevisit(Event p, Event r,
            std::unique_ptr<ReadLabel> read, std::unique_ptr<WriteLabel> write)
		: Revisit(RV_Rev_HB_PREDS_XMM, p),
		  ReadRevisit(RV_Rev_HB_PREDS_XMM, r),
		  XMMRevisit(std::move(read), std::move(write))
    {}

	static bool classof(const Revisit *item) {
		return item->getKind() == RV_Rev_HB_PREDS_XMM;
    }
};

class ReadForwardRacyReadTidXMMRevisit : public ReadForwardRevisit, public XMMRevisit {
public:
	ReadForwardRacyReadTidXMMRevisit() = delete;
	ReadForwardRacyReadTidXMMRevisit(Event p, Event r, std::unique_ptr<ReadLabel> read, std::unique_ptr<WriteLabel> write)
		: ReadForwardRevisit(RV_FRevRacyReadTidXMM, p, r, false),
		XMMRevisit(std::move(read), std::move(write))
    {}

	static bool classof(const Revisit *item) {
		return item->getKind() == RV_FRevRacyReadTidXMM;
	}
};

class CommittedWriteXMMRevisit : public ReadForwardRevisit, public XMMRevisit {
public:
	CommittedWriteXMMRevisit() = delete;
	CommittedWriteXMMRevisit(Event p, Event r, std::unique_ptr<ReadLabel> read, std::unique_ptr<WriteLabel> write, std::unordered_set<Event, EventHasher> committedEvents)
		: ReadForwardRevisit(RV_CommittedWriteXMM, p, r, false),
		XMMRevisit(std::move(read), std::move(write)),
		committedEvents(std::move(committedEvents))
    {}

	std::unordered_set<Event, EventHasher> committedEvents;

	static bool classof(const Revisit *item) {
		return item->getKind() == RV_CommittedWriteXMM;
	}
};

/*******************************************************************************
 **                             Static methods
 *******************************************************************************/

inline Revisit *Revisit::castFromReadRevisit(const ReadRevisit *r)
{
	auto rk = r->getRevisitKind();
	switch (rk) {
	case Revisit::Kind::RV_FRevRead:
		return static_cast<ReadForwardRevisit *>(const_cast<ReadRevisit *>(r));
	case Revisit::Kind::RV_BRev:
		return static_cast<BackwardRevisit *>(const_cast<ReadRevisit *>(r));
	case Revisit::Kind::RV_BRevHelper:
		return static_cast<BackwardRevisitHELPER *>(const_cast<ReadRevisit *>(r));
	case Revisit::Kind::RV_BRevXMM:
		return static_cast<BackwardXMMRevisit *>(const_cast<ReadRevisit *>(r));
	default:
		BUG();
	}
}

inline ReadRevisit *Revisit::castToReadRevisit(const Revisit *r)
{
	auto rk = r->getKind();
	switch (rk) {
	case Revisit::Kind::RV_FRevRead:
		return static_cast<ReadForwardRevisit *>(const_cast<Revisit *>(r));
	case Revisit::Kind::RV_BRev:
		return static_cast<BackwardRevisit *>(const_cast<Revisit *>(r));
	case Revisit::Kind::RV_BRevHelper:
		return static_cast<BackwardRevisitHELPER *>(const_cast<Revisit *>(r));
	case Revisit::Kind::RV_BRevXMM:
		return static_cast<BackwardXMMRevisit *>(const_cast<Revisit *>(r));
	case Revisit::Kind::RV_FRevXMM:
		return static_cast<ReadForwardXMMRevisit *>(const_cast<Revisit *>(r));
	default:
		BUG();
	}
}


/*******************************************************************************
 **                             RTTI helpers
 *******************************************************************************/

/* Specialization selected when ToTy is not a known subclass of ReadRevisit */
template <class ToTy,
	  bool IsKnownSubtype = ::std::is_base_of<ReadRevisit, ToTy>::value>
struct cast_convert_read_rev {
	static const ToTy *doit(const ReadRevisit *Val) {
		return static_cast<const ToTy*>(Revisit::castFromReadRevisit(Val));
	}

	static ToTy *doit(ReadRevisit *Val) {
		return static_cast<ToTy*>(Revisit::castFromReadRevisit(Val));
	}
};

/* Specialization selected when ToTy is a known subclass of ReadRevisit */
template <class ToTy>
struct cast_convert_read_rev<ToTy, true> {
	static const ToTy *doit(const ReadRevisit *Val) {
		return static_cast<const ToTy*>(Val);
	}

	static ToTy *doit(ReadRevisit *Val) {
		return static_cast<ToTy*>(Val);
	}
};

namespace llvm {

	/* isa<T>(ReadRevisit *) */
	template <typename To>
	struct isa_impl<To, ::ReadRevisit> {
		static bool doit(const ::ReadRevisit &Val) {
			return To::classofKind(Val.getRevisitKind());
		}
	};

	/* cast<T>(ReadRevisit *) */
	template<class ToTy>
	struct cast_convert_val<ToTy,
				const ::ReadRevisit,const ::ReadRevisit> {
		static const ToTy &doit(const ::ReadRevisit &Val) {
			return *::cast_convert_read_rev<ToTy>::doit(&Val);
		}
	};

	template<class ToTy>
	struct cast_convert_val<ToTy, ::ReadRevisit, ::ReadRevisit> {
		static ToTy &doit(::ReadRevisit &Val) {
			return *::cast_convert_read_rev<ToTy>::doit(&Val);
		}
	};

	template<class ToTy>
	struct cast_convert_val<ToTy,
				const ::ReadRevisit*, const ::ReadRevisit*> {
		static const ToTy *doit(const ::ReadRevisit *Val) {
			return ::cast_convert_read_rev<ToTy>::doit(Val);
		}
	};

	template<class ToTy>
	struct cast_convert_val<ToTy, ::ReadRevisit*, ::ReadRevisit*> {
		static ToTy *doit(::ReadRevisit *Val) {
			return ::cast_convert_read_rev<ToTy>::doit(Val);
		}
	};

	/// Implement cast_convert_val for EventLabel -> ReadRevisit conversions.
	template<class FromTy>
	struct cast_convert_val< ::ReadRevisit, FromTy, FromTy> {
		static ::ReadRevisit &doit(const FromTy &Val) {
			return *FromTy::castToReadRevisit(&Val);
		}
	};

	template<class FromTy>
	struct cast_convert_val< ::ReadRevisit, FromTy*, FromTy*> {
		static ::ReadRevisit *doit(const FromTy *Val) {
			return FromTy::castToReadRevisit(Val);
		}
	};

	template<class FromTy>
	struct cast_convert_val< const ::ReadRevisit, FromTy, FromTy> {
		static const ::ReadRevisit &doit(const FromTy &Val) {
			return *FromTy::castToReadRevisit(&Val);
		}
	};

	template<class FromTy>
	struct cast_convert_val< const ::ReadRevisit, FromTy*, FromTy*> {
		static const ::ReadRevisit *doit(const FromTy *Val) {
			return FromTy::castToReadRevisit(Val);
		}
	};

} /* namespace llvm */


#endif /* __REVISIT_HPP__ */
