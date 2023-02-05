#include <featureTests.h>
#ifdef ROSE_ENABLE_BINARY_ANALYSIS
#include <sage3basic.h>
#include <Rose/BinaryAnalysis/InstructionSemantics/BaseSemantics/SValue.h>
#include <Rose/BinaryAnalysis/InstructionSemantics/BaseSemantics/RiscOperators.h>

#include <Rose/BinaryAnalysis/InstructionSemantics/BaseSemantics/Formatter.h>
#include <sstream>

namespace Rose {
namespace BinaryAnalysis {
namespace InstructionSemantics {
namespace BaseSemantics {

size_t
SValue::nBits() const {
    return get_width();
}

bool
SValue::isConcrete() const {
    return is_number();
}

Sawyer::Optional<uint64_t>
SValue::toUnsigned() const {
    if (isConcrete() && nBits() <= 64) {
        return get_number();
    } else {
        return Sawyer::Nothing();
    }
}

Sawyer::Optional<int64_t>
SValue::toSigned() const {
    if (auto val = toUnsigned()) {
        uint64_t uval = BitOps::signExtend(*val, nBits());
        int64_t ival = static_cast<int64_t>(uval);

        // The above static_cast is implementation defined when uval >= 2^63, but the cast from signed to unsigned doesn't have
        // implementation defined behavior. This allows us to check that the above static cast did what we want.
        ASSERT_require2(static_cast<uint64_t>(ival) == uval, "this compiler's unsigned-to-signed static_cast is strange");
        return ival;
    } else {
        return Sawyer::Nothing();
    }
}

bool
SValue::mustEqual(const SValue::Ptr &other, const SmtSolverPtr &solver) const {
    return must_equal(other, solver);
}

bool
SValue::mayEqual(const SValue::Ptr &other, const SmtSolverPtr &solver) const {
    return may_equal(other, solver);
}

bool
SValue::mayAlias(const SValue::Ptr &other, size_t ourWidth, size_t theirWidth, RiscOperators *ops) {
    return may_alias(other, ourWidth, theirWidth, ops);
}

bool
SValue::mustAlias(const SValue::Ptr &other, size_t ourWidth, size_t theirWidth, RiscOperators *ops) {
    return must_alias(other, ourWidth, theirWidth, ops);
}

bool
SValue::must_alias(const SValue::Ptr &other, size_t ourWidth, size_t theirWidth, RiscOperators *ops) {
    // Check the easy case: two one-byte cells must alias one another if their address must be equal.
    if (8==ourWidth && 8==theirWidth)
        return this->mustEqual(other, ops->solver());

    // if lo1==lo2, then hi1>=lo1==lo2 and hi2>=lo2==lo1, satisfying the condition below.
    if (this->mustEqual(other, ops->solver())) {
        return true;
    }

    size_t addr_nbits = this->nBits();
    ASSERT_require(other->nBits()==addr_nbits);

    ASSERT_require(ourWidth % 8 == 0);
    SValue::Ptr lo1(this);
    SValue::Ptr hi1 = ops->add(lo1, ops->number_(lo1->nBits(), ourWidth / 8));

    ASSERT_require(theirWidth % 8 == 0);
    SValue::Ptr lo2 = other;
    SValue::Ptr hi2 = ops->add(lo2, ops->number_(lo2->nBits(), theirWidth / 8));

    // Two cells must_alias iff hi2 >= lo1 and hi1 >= lo2. Two things complicate this: first, the values might not be known
    // quantities, depending on the semantic domain.  Second, the RiscOperators does not define a greater-than-or-equal
    // operation, so we need to write it in terms of a subtraction. See x86 CMP and JG instructions for examples. ("sf" is sign
    // flag, "of" is overflow flag.)
    SValue::Ptr carries;
    SValue::Ptr diff = ops->addWithCarries(hi2, ops->invert(lo1), ops->boolean_(true), carries/*out*/);
    SValue::Ptr sf = ops->extract(diff, addr_nbits-1, addr_nbits);
    SValue::Ptr of = ops->xor_(ops->extract(carries, addr_nbits-1, addr_nbits),
                                 ops->extract(carries, addr_nbits-2, addr_nbits-1));
    SValue::Ptr cond1 = ops->invert(ops->xor_(sf, of));
    diff = ops->addWithCarries(hi1, ops->invert(lo2), ops->boolean_(true), carries/*out*/);
    sf = ops->extract(diff, addr_nbits-1, addr_nbits);
    of = ops->xor_(ops->extract(carries, addr_nbits-1, addr_nbits),
                       ops->extract(carries, addr_nbits-2, addr_nbits-1));
    SValue::Ptr cond2 = ops->invert(ops->xor_(sf, of));
    SValue::Ptr overlap = ops->and_(cond1, cond2);
    return overlap->isTrue();
}

bool
SValue::may_alias(const SValue::Ptr &other, size_t ourWidth, size_t theirWidth, RiscOperators *ops) {
    // Check for the easy case:  two one-byte cells may alias one another if their addresses may be equal.
    if (8==ourWidth && 8==theirWidth)
        return this->mayEqual(other, ops->solver());

    size_t addr_nbits = this->nBits();
    ASSERT_require(other->nBits()==addr_nbits);

    ASSERT_require(ourWidth % 8 == 0);       // memory is byte addressable, so values must be multiples of a byte
    SValue::Ptr lo1(this);
    SValue::Ptr hi1 = ops->add(lo1, ops->number_(lo1->nBits(), ourWidth / 8));

    ASSERT_require(theirWidth % 8 == 0);
    SValue::Ptr lo2 = other;
    SValue::Ptr hi2 = ops->add(lo2, ops->number_(lo2->nBits(), theirWidth / 8));

    // Two cells may_alias iff we can prove that they are not disjoint.  The two cells are disjoint iff lo2 >= hi1 or lo1 >=
    // hi2. Two things complicate this: first, the values might not be known quantities, depending on the semantic domain.
    // Second, the RiscOperators does not define a greater-than-or-equal operation, so we need to write it in terms of a
    // subtraction. See x86 CMP and JG instructions for examples. ("sf" is sign flag, "of" is overflow flag.)
    SValue::Ptr carries;
    SValue::Ptr diff = ops->addWithCarries(lo2, ops->invert(hi1), ops->boolean_(true), carries/*out*/);
    SValue::Ptr sf = ops->extract(diff, addr_nbits-1, addr_nbits);
    SValue::Ptr of = ops->xor_(ops->extract(carries, addr_nbits-1, addr_nbits),
                                 ops->extract(carries, addr_nbits-2, addr_nbits-1));
    SValue::Ptr cond1 = ops->invert(ops->xor_(sf, of));
    diff = ops->addWithCarries(lo1, ops->invert(hi2), ops->boolean_(true), carries/*out*/);
    sf = ops->extract(diff, addr_nbits-1, addr_nbits);
    of = ops->xor_(ops->extract(carries, addr_nbits-1, addr_nbits),
                       ops->extract(carries, addr_nbits-2, addr_nbits-1));
    SValue::Ptr cond2 = ops->invert(ops->xor_(sf, of));
    SValue::Ptr disjoint = ops->or_(cond1, cond2);
    return !disjoint->isTrue();
}

bool
SValue::isTrue() const {
    return toUnsigned().orElse(0) != 0;
}

bool
SValue::isFalse() const {
    return toUnsigned().orElse(1) == 0;
}

std::string
SValue::comment() const {
    return get_comment();
}

void
SValue::comment(const std::string &s) const {
    set_comment(s);
}

std::ostream&
operator<<(std::ostream &o, const SValue &x) {
    x.print(o);
    return o;
}

std::ostream&
operator<<(std::ostream &o, const SValue::WithFormatter &x) {
    x.print(o);
    return o;
}

void
SValue::print(std::ostream &stream) const {
    Formatter fmt;
    print(stream, fmt);
}

SValue::WithFormatter
SValue::operator+(const std::string &linePrefix) {
    static Formatter fmt;
    fmt.set_line_prefix(linePrefix);
    return with_format(fmt);
}

std::string
SValue::toString() const {
    std::ostringstream ss;
    print(ss);
    return ss.str();
}

} // namespace
} // namespace
} // namespace
} // namespace

BOOST_CLASS_EXPORT_IMPLEMENT(Rose::BinaryAnalysis::InstructionSemantics::BaseSemantics::SValue);

#endif
