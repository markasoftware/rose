#include <featureTests.h>
#ifdef ROSE_ENABLE_BINARY_ANALYSIS
#include <sage3basic.h>
#include <Rose/BinaryAnalysis/InstructionSemantics/BaseSemantics/MemoryCell.h>

#include <Rose/BinaryAnalysis/InstructionSemantics/BaseSemantics/Formatter.h>
#include <Rose/BinaryAnalysis/InstructionSemantics/BaseSemantics/RiscOperators.h>
#include <Rose/BinaryAnalysis/InstructionSemantics/BaseSemantics/SValue.h>
#include <Rose/BinaryAnalysis/InstructionSemantics/Utility.h>

#include <boost/enable_shared_from_this.hpp>

namespace Rose {
namespace BinaryAnalysis {
namespace InstructionSemantics {
namespace BaseSemantics {

MemoryCell::MemoryCell() {}

MemoryCell::MemoryCell(const SValue::Ptr &address, const SValue::Ptr &value)
    : address_(address), value_(value) {
    ASSERT_not_null(address);
    ASSERT_not_null(value);
}

MemoryCell::MemoryCell(const MemoryCell &other)
    : boost::enable_shared_from_this<MemoryCell>(other) {
    address_ = other.address_->copy();
    value_ = other.value_->copy();
    writers_ = other.writers_;
    ioProperties_ = other.ioProperties_;
    position_ = other.position_;
}

MemoryCell::~MemoryCell() {}

SValue::Ptr
MemoryCell::address() const {
    return address_;
}

void
MemoryCell::address(const SValue::Ptr &addr) {
    ASSERT_not_null(addr);
    address_ = addr;
}

SValue::Ptr
MemoryCell::value() const {
    return value_;
}

void
MemoryCell::value(const SValue::Ptr &v) {
    ASSERT_not_null(v);
    value_ = v;
}

bool
MemoryCell::NonWrittenCells::operator()(const MemoryCell::Ptr &cell) {
    return cell->getWriters().isEmpty();
}

bool
MemoryCell::mayAlias(const MemoryCell::Ptr &other, RiscOperators *addrOps) const
{
    return address_->mayAlias(other->address(), value_->nBits(), other->value()->nBits(), addrOps);
}

bool
MemoryCell::mustAlias(const MemoryCell::Ptr &other, RiscOperators *addrOps) const
{
    return address_->mustAlias(other->address(), value_->nBits(), other->value()->nBits(), addrOps);
}

void
MemoryCell::hash(Combinatorics::Hasher &hasher) const {
    ASSERT_not_null(address_);
    address_->hash(hasher);
    ASSERT_not_null(value_);
    value_->hash(hasher);
}

void
MemoryCell::print(std::ostream &stream) const {
    Formatter fmt;
    print(stream, fmt);
}

void
MemoryCell::print(std::ostream &stream, Formatter &fmt) const
{
    stream <<"addr=" <<(*address_+fmt);

    if (fmt.get_show_latest_writers()) {
        const AddressSet &writers = getWriters();
        if (writers.isEmpty()) {
            // nothing to show
        } else if (writers.size() == 1) {
            stream <<" writer=" <<StringUtility::addrToString(*writers.values().begin());
        } else {
            stream <<" writers=[";
            for (AddressSet::ConstIterator iter=writers.values().begin(); iter!=writers.values().end(); ++iter) {
                stream <<(iter==writers.values().begin() ? "" : ", ")
                       <<StringUtility::addrToString(*iter);
            }
            stream <<"]";
        }
    }

    // FIXME[Robb P. Matzke 2015-08-12]: This doesn't take into account all combinations of properties -- just a few of the
    // more common ones.
    if (fmt.get_show_properties()) {
        if (ioProperties_.exists(IO_READ_BEFORE_WRITE)) {
            stream <<" read-before-write";
        } else if (ioProperties_.exists(IO_WRITE) && ioProperties_.exists(IO_READ)) {
            // nothing
        } else if (ioProperties_.exists(IO_READ)) {
            stream <<" read-only";
        } else if (ioProperties_.exists(IO_WRITE)) {
            stream <<" write-only";
        }
    }

    stream <<" value=" <<(*value_+fmt);
}

MemoryCell::WithFormatter
MemoryCell::with_format(Formatter &fmt) {
    return WithFormatter(shared_from_this(), fmt);
}

MemoryCell::WithFormatter
MemoryCell::operator+(Formatter &fmt) {
    return with_format(fmt);
}

MemoryCell::WithFormatter
MemoryCell::operator+(const std::string &linePrefix) {
    static Formatter fmt;
    fmt.set_line_prefix(linePrefix);
    return with_format(fmt);
}

void
MemoryCell::setWriter(rose_addr_t writerVa) {
    eraseWriters();
    writers_.insert(writerVa);
}

std::ostream& operator<<(std::ostream &o, const MemoryCell &x) {
    x.print(o);
    return o;
}

std::ostream& operator<<(std::ostream &o, const MemoryCell::WithFormatter &x) {
    x.print(o);
    return o;
}

} // namespace
} // namespace
} // namespace
} // namespace

BOOST_CLASS_EXPORT_IMPLEMENT(Rose::BinaryAnalysis::InstructionSemantics::BaseSemantics::MemoryCell);

#endif
