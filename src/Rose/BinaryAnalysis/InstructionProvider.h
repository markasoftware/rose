#ifndef ROSE_BinaryAnalysis_InstructionProvider_H
#define ROSE_BinaryAnalysis_InstructionProvider_H
#include <featureTests.h>
#ifdef ROSE_ENABLE_BINARY_ANALYSIS

#include <Rose/BinaryAnalysis/BasicTypes.h>
#include <Rose/BinaryAnalysis/CallingConvention.h>
#include <Rose/BinaryAnalysis/Disassembler/BasicTypes.h>
#include <Rose/BinaryAnalysis/InstructionSemantics/BaseSemantics.h>
#include "AstSerialization.h"

#include <boost/serialization/access.hpp>
#include <Sawyer/Assert.h>
#include <Sawyer/HashMap.h>
#include <Sawyer/SharedPointer.h>

namespace Rose {
namespace BinaryAnalysis {

/** Provides and caches instructions.
 *
 *  This class returns an instruction for a given address, caching the instruction so that the same instruction is returned
 *  each time the same address is specified.  If an instruction cannot be returned because it doesn't exist then a null pointer
 *  should be returned.  If an instruction cannot be disassembled at the specified address then an "unknown" instruction should
 *  be returned.
 *
 *  An instruction provider normally uses a supplied disassembler to obtain instructions that aren't in its cache.  However,
 *  the user can initialize the cache explicitly and turn off the ability to call a disassembler.  A disassembler is always
 *  required regardless of whether its used to obtain new instructions because the disassembler has the canonical information
 *  about the machine architecture: what registers are defined, which registers are the program counter and stack pointer,
 *  which instruction semantics dispatcher can be used with the instructions, etc. */
class InstructionProvider: public Sawyer::SharedObject {
public:
    /** Shared-ownership pointer. */
    typedef Sawyer::SharedPointer<InstructionProvider> Ptr;

    /** Mapping from address to instruction. */
    typedef Sawyer::Container::HashMap<rose_addr_t, SgAsmInstruction*> InsnMap;

private:
    Disassembler::BasePtr disassembler_;
    MemoryMap::Ptr memMap_;
    mutable InsnMap insnMap_;                           // this is a cache
    bool useDisassembler_;

#ifdef ROSE_HAVE_BOOST_SERIALIZATION_LIB
private:
    friend class boost::serialization::access;

    template<class S>
    void save(S &s, const unsigned /*version*/) const {
        roseAstSerializationRegistration(s);            // so we can save instructions through SgAsmInstruction base ptrs
        bool hasDisassembler = disassembler_ != NULL;
        s <<BOOST_SERIALIZATION_NVP(hasDisassembler);
        s <<BOOST_SERIALIZATION_NVP(useDisassembler_);
        s <<BOOST_SERIALIZATION_NVP(memMap_);
        s <<BOOST_SERIALIZATION_NVP(insnMap_);
        if (hasDisassembler) {
            std::string disName = Disassembler::name(disassembler_);
            s <<BOOST_SERIALIZATION_NVP(disName);
        }
    }

    template<class S>
    void load(S &s, const unsigned /*version*/) {
        roseAstSerializationRegistration(s);
        bool hasDisassembler = false;
        s >>BOOST_SERIALIZATION_NVP(hasDisassembler);
        s >>BOOST_SERIALIZATION_NVP(useDisassembler_);
        s >>BOOST_SERIALIZATION_NVP(memMap_);
        s >>BOOST_SERIALIZATION_NVP(insnMap_);
        if (hasDisassembler) {
            std::string disName;
            s >>BOOST_SERIALIZATION_NVP(disName);
            disassembler_ = Disassembler::lookup(disName);
            ASSERT_not_null2(disassembler_, "disassembler name=" + disName);
        }
    }

    BOOST_SERIALIZATION_SPLIT_MEMBER();
#endif

protected:
    InstructionProvider();

    InstructionProvider(const Disassembler::BasePtr &disassembler, const MemoryMap::Ptr &map);

public:
    ~InstructionProvider();

    /** Static allocating Constructor.
     *
     *  The disassembler is required even if the user plans to turn off the ability to obtain instructions from the
     *  disassembler.  The memory map should be configured so that all segments that potentially contain instructions have
     *  execute permission.  Any readable/nonwritable segments will be considered to be constant for the life of the specimen.
     *  For instance, if a linking step has initialized the dynamic linking tables then those tables can be marked as readable
     *  and non-writable so that indirect jumps through the table will result in concrete execution addresses.
     *
     *  The disassembler is owned by the caller and should not be freed until after the instruction provider is destroyed.  The
     *  memory map is copied into the instruction provider. */
    static Ptr instance(const Disassembler::BasePtr &disassembler, const MemoryMap::Ptr &map) {
        return Ptr(new InstructionProvider(disassembler, map));
    }

    /** Enable or disable the disassembler.
     *
     *  When the disassembler is disabled then it is not called when a new instruction is needed, but rather a null instruction
     *  pointer is returned (and cached).
     *
     * @{ */
    bool isDisassemblerEnabled() const {
        return useDisassembler_;
    }
    void enableDisassembler(bool enable=true);
    void disableDisassembler() {
        useDisassembler_ = false;
    }
    /** @} */

    /** Returns the instruction at the specified virtual address, or null.
     *
     *  If the virtual address is non-executable then a null pointer is returned, otherwise either a valid instruction or an
     *  "unknown" instruction is returned.  An "unknown" instruction is used for cases where a valid instruction could not be
     *  disassembled, including the case when the first byte of a multi-byte instruction is executable but the remaining bytes
     *  are not executable. */
    SgAsmInstruction* operator[](rose_addr_t va) const;

    /** Insert an instruction into the cache.
     *
     *  This instruction provider saves a pointer to the instruction without taking ownership.  If an instruction already
     *  exists at the new instruction's address then the new instruction replaces the old instruction. */
    void insert(SgAsmInstruction*);

    /** Returns the disassembler.
     *
     *  Returns the disassembler pointer provided in the constructor.  The disassembler is not owned by this instruction
     *  provider, but must not be freed until after the instruction provider is destroyed. */
    Disassembler::BasePtr disassembler() const;

    /** Returns number of cached starting addresses.
     *
     *  The number of cached starting addresses includes those addresses where an instruction exists, and those addresses where
     *  an instruction is known to not exist.
     *
     *  This is a constant-time operation. */
    size_t nCached() const { return insnMap_.size(); }

    /** Returns the register dictionary. */
    RegisterDictionaryPtr registerDictionary() const;

    /** Returns the calling convention dictionary. */
    const CallingConvention::Dictionary& callingConventions() const;

    /** Register used as the instruction pointer. */
    RegisterDescriptor instructionPointerRegister() const;

    /** Register used as a user-mode stack pointer. */
    RegisterDescriptor stackPointerRegister() const;

    /** Register used for function call frames.
     *
     *  Not all architectures have such a register, in which case a default-constructed register descriptor is returned. */
    RegisterDescriptor stackFrameRegister() const;

    /** Register holding a function call's return address.
     *
     *  Not all architectures have such a register, in which case a default-constructed register descriptor is returned. Some
     *  architectures call this a "link" register (e.g., PowerPC). */
    RegisterDescriptor callReturnRegister() const;

    /** Register used as a segment to access stack memory.
     *
     *  Not all architectures have such a register, in which case a default-constructed register descriptor is returned. */
    RegisterDescriptor stackSegmentRegister() const;

    /** Default memory byte order. */
    ByteOrder::Endianness defaultByteOrder() const;

    /** Word size in bits. */
    size_t wordSize() const;

    /** Alignment requirement for instructions. */
    size_t instructionAlignment() const;

    /** Instruction dispatcher.
     *
     *  Returns a pointer to a dispatcher used for instruction semantics.  Not all architectures support instruction semantics,
     *  in which case a null pointer is returned.  The returned dispatcher is not connected to any semantic domain, so it can
     *  only be used to call its virtual constructor to create a valid dispatcher. */
    InstructionSemantics::BaseSemantics::DispatcherPtr dispatcher() const;

    /** Print some partitioner performance statistics. */
    void showStatistics() const;
};

} // namespace
} // namespace

#endif
#endif
