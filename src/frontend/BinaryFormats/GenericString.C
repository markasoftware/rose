/* Strings. Uniform treatment for strings stored in a binary file and strings generated on the fly. */
#include <featureTests.h>
#ifdef ROSE_ENABLE_BINARY_ANALYSIS
#include "sage3basic.h"

using namespace Rose;

std::string
SgAsmGenericString::get_string(bool /*escape*/) const
{
    ROSE_ASSERT(!"should have been pure virtual if ROSETTA supported that.");
    abort();

    // DQ (11/27/2009): MSVC requires a return stmt for any non-void return type of a function.
    return "error in SgAsmGenericString::get_string()";
}

void
SgAsmGenericString::set_string(const std::string&)
{
    ROSE_ASSERT(!"should have been pure virtual if ROSETTA supported that.");
    abort();
}

void
SgAsmGenericString::set_string(rose_addr_t /*offset*/)
{
    ROSE_ASSERT(!"should have been pure virtual if ROSETTA supported that.");
    abort();
}

void
SgAsmGenericString::dump(FILE*, const char */*prefix*/, ssize_t /*idx*/) const
{
    ROSE_ASSERT(!"should have been pure virtual if ROSETTA supported that.");
    abort();
}

/* Constructor */
void
SgAsmBasicString::ctor()
{
#if 0
    fprintf(stderr, "SgAsmBasicString::ctor this=0x%08lx\n", (unsigned long)this);
    if (this==(void*)0x685998)
        abort(); /*DEBUGGING (rpm 2008-10-10)*/
#endif
}

/* Override ROSETTA because generated code doesn't match virtual signature in base class */
std::string
SgAsmBasicString::get_string(bool escape) const
{
    if (escape)
        return escapeString(p_string);
    return p_string;
}
void
SgAsmBasicString::set_string(const std::string &s)
{
    if (p_string!=s)
        set_isModified(true);
    p_string = s;
}
void
SgAsmBasicString::set_string(rose_addr_t offset)
{
    ASSERT_not_implemented("set_string(rose_addr_t offset=" + StringUtility::addrToString(offset) + ")");
}

void
SgAsmBasicString::dump(FILE *f, const char *prefix, ssize_t idx) const
{
    char p[4096];
    if (idx>=0) {
        sprintf(p, "%sBasicString[%zd].", prefix, idx);
    } else {
        sprintf(p, "%sBasicString.", prefix);
    }
    int w = std::max(1, DUMP_FIELD_WIDTH-(int)strlen(p));
    fprintf(f, "%s%-*s = \"%s\"\n", p, w, "value", get_string(true).c_str());
}
    
void
SgAsmStoredString::ctor(SgAsmGenericStrtab *strtab, rose_addr_t offset, bool shared)
{
    p_storage = strtab->create_storage(offset, shared);
}
void
SgAsmStoredString::ctor(SgAsmGenericStrtab *strtab, const std::string &s)
{
    p_storage = strtab->create_storage(0, false);
    set_string(s);
}
void
SgAsmStoredString::ctor(SgAsmStringStorage *storage)
{
    p_storage = storage;
}
#if 0
// DQ (9/9/2008): Use the destructor built automatically by ROSETTA.
SgAsmStoredString::~SgAsmStoredString()
{
#if 0 /* FIXME: Strings may share storage, so we can't free it. (RPM 2008-09-03) */
    /* Free storage if it isn't associated with a string table. */
    if (p_storage && NULL==p_storage->strtab)
        delete p_storage;
#endif
    p_storage = NULL;
}
#endif

std::string
SgAsmStoredString::get_string(bool escape) const 
{
    std::string retval = get_storage()->get_string();
    if (escape)
        retval = escapeString(retval);
    return retval;
}

rose_addr_t
SgAsmStoredString::get_offset() const
{
    if (NULL==get_storage())
        return unallocated;
    if (get_storage()->get_offset() == unallocated) {
        SgAsmGenericStrtab *strtab = get_storage()->get_strtab();
        ROSE_ASSERT(strtab!=NULL);
        strtab->reallocate(false);
        ROSE_ASSERT(get_storage()->get_offset() != unallocated);
    }
    return get_storage()->get_offset();
}

SgAsmGenericStrtab *
SgAsmStoredString::get_strtab() 
{
    return get_storage()->get_strtab();
}

void
SgAsmStoredString::set_string(const std::string &s)
{
    if (get_string()==s) return; /* no change in value */
    set_isModified(true);
    SgAsmStringStorage *storage = get_storage();
    ROSE_ASSERT(storage!=NULL); /* we don't even know which string table! */
    storage->get_strtab()->free(storage);
    storage->set_string(s);
}

void
SgAsmStoredString::set_string(rose_addr_t offset)
{
    set_isModified(true);
    SgAsmStringStorage *storage = get_storage();
    ROSE_ASSERT(storage!=NULL); /* we don't even know which string table! */
    storage->get_strtab()->rebind(storage, offset);
}

/* Print some debugging info */
void
SgAsmStoredString::dump(FILE *f, const char *prefix, ssize_t idx) const
{
    char p[4096];
    if (idx>=0) {
        sprintf(p, "%sStoredString[%zd].", prefix, idx);
    } else {
        sprintf(p, "%sStoredString.", prefix);
    }
    int w = std::max(1, DUMP_FIELD_WIDTH-(int)strlen(p));
    
    fprintf(f, "%s%-*s = 0x%08lx\n", p, w, "storage", (unsigned long)get_storage());
    if (get_storage())
        get_storage()->dump(f, p, -1);
}

/* Print some debugging info */
void
SgAsmStringStorage::dump(FILE *f, const char *prefix, ssize_t idx) const
{
    char p[4096];
    if (idx>=0) {
        sprintf(p, "%sStringStorage[%zd].", prefix, idx);
    } else {
        sprintf(p, "%sStringStorage.", prefix);
    }
    int w = std::max(1, DUMP_FIELD_WIDTH-(int)strlen(p));
    
    fprintf(f, "%s%-*s =", p, w, "sec,offset,val");
    SgAsmGenericStrtab *strtab = get_strtab();
    if (strtab) {
        fprintf(f, " section [%d] \"%s\"",
                strtab->get_container()->get_id(),
                strtab->get_container()->get_name()->get_string(true).c_str());
    } else {
        fputs(" no section", f);
    }
    if (!strtab || get_offset()==SgAsmGenericString::unallocated) {
        fputs(", not allocated", f);
    } else {
        fprintf(f, ", offset 0x%08" PRIx64 " (%" PRIu64 ")", get_offset(), get_offset());
    }
    fprintf(f, ", \"%s\"\n", escapeString(get_string()).c_str());
}

SgAsmStoredString *
SgAsmGenericStrtab::create_string(rose_addr_t offset, bool shared)
{
    SgAsmStringStorage *storage = create_storage(offset, shared);
    return new SgAsmStoredString(storage);
}

void
SgAsmGenericStrtab::free(SgAsmStringStorage *storage)
{
    ROSE_ASSERT(storage!=NULL);
    ROSE_ASSERT(storage!=p_dont_free);
    rose_addr_t old_offset = storage->get_offset();
    if (old_offset!=SgAsmGenericString::unallocated) {
        set_isModified(true);
        storage->set_offset(SgAsmGenericString::unallocated);
        free(old_offset, storage->get_string().size()+1);
    }
}

void
SgAsmGenericStrtab::free(rose_addr_t offset, rose_addr_t size)
{
    if (offset==SgAsmGenericString::unallocated || 0==size)
        return;

    ROSE_ASSERT(offset+size <= get_container()->get_size());
    set_isModified(true);
    
    /* Make sure area is not already in free list.  The freelist.insert() handles this gracefully, but if we're freeing
     * something that's already in the list then we have a logic error somewhere. */
    ROSE_ASSERT(!get_freelist().overlaps(AddressInterval::baseSize(offset, size)));

    /* Preserve anything that's still referenced. The caller should have assigned SgAsmStoredString::unalloced to the "offset"
     * member of the string storage to indicate that it's memory in the string table is no longer in use. */
    AddressIntervalSet toFree;
    toFree.insert(AddressInterval::baseSize(offset, size));
    for (size_t i=0; i<p_storage_list.size(); i++) {
        SgAsmStringStorage *storage = p_storage_list[i];
        if (storage->get_offset()!=SgAsmGenericString::unallocated)
            toFree.erase(AddressInterval::baseSize(storage->get_offset(), get_storage_size(storage)));
    }

    /* Add un-referenced extents to free list. */
    get_freelist().insertMultiple(toFree);
}

void
SgAsmGenericStrtab::free_all_strings(bool blow_away_holes)
{
    SgAsmGenericSection *container = get_container();
    SgAsmGenericFile *file = container->get_file();
    bool is_tracking = file->get_tracking_references();
    set_isModified(true);

    /* Mark all storage objects as being unallocated. Never free the dont_free storage (if any). */
    for (size_t i=0; i<p_storage_list.size(); i++) {
        if (p_storage_list[i]->get_offset()!=SgAsmGenericString::unallocated && p_storage_list[i]!=p_dont_free) {
            p_num_freed++;
            p_storage_list[i]->set_offset(SgAsmGenericString::unallocated);
        }
    }

    /* Mark holes as referenced */
    if (blow_away_holes) {
        file->set_tracking_references(true);
        file->mark_referenced_extent(container->get_offset(), container->get_size());
        file->set_tracking_references(is_tracking);
    }

    /* The free list is everything that's been referenced in the container section. */
    get_freelist() = container->get_referenced_extents();

    /* Remove the empty string from the free list */
    if (p_dont_free)
        get_freelist().erase(AddressInterval::baseSize(p_dont_free->get_offset(), p_dont_free->get_string().size()+1));
}

bool
SgAsmGenericStrtab::reallocate(bool shrink)
{
    bool reallocated = false;
    SgAsmGenericSection *container = get_container();
    rose_addr_t extend_size = 0;                                     /* amount by which to extend string table */

    /* Get list of strings that need to be allocated and sort by descending size. */
    std::vector<size_t> map;
    for (size_t i=0; i<p_storage_list.size(); i++) {
        SgAsmStringStorage *storage = p_storage_list[i];
        if (storage->get_offset()==SgAsmGenericString::unallocated) {
            map.push_back(i);
        }
    }
    for (size_t i=1; i<map.size(); i++) {
        for (size_t j=0; j<i; j++) {
            if (p_storage_list[map[j]]->get_string().size() < p_storage_list[map[i]]->get_string().size()) {
                size_t x = map[i];
                map[i] = map[j];
                map[j] = x;
            }
        }
    }

    /* Allocate from largest to smallest so we have the best chance of finding overlaps */
    for (size_t i=0; i<map.size(); i++) {
        SgAsmStringStorage *storage = p_storage_list[map[i]];
        ROSE_ASSERT(storage->get_offset()==SgAsmGenericString::unallocated);

        /* We point empty strings at the dont_free storage if possible. */
        if (storage->get_string()=="" && p_dont_free) {
            ROSE_ASSERT(p_dont_free->get_string()=="");
            storage->set_offset(0);
        }

        /* If there's already a string with the same value then they can share space in the string table. They're still
         * considered two separate strings, so changing one doesn't affect the other. */
        if (storage->get_offset()==SgAsmGenericString::unallocated) {
            for (size_t j=0; j<p_storage_list.size(); j++) {
                SgAsmStringStorage *previous = p_storage_list[j];
                if (previous->get_offset()!=SgAsmGenericString::unallocated && previous->get_string()==storage->get_string()) {
                    storage->set_offset(previous->get_offset());
                    break;
                }
            }
        }

        /* Some string tables may be able to overlap strings. For instance, ELF can overlap "domain" and "main" since it
         * encodes strings with NUL termination. */
        if (storage->get_offset()==SgAsmGenericString::unallocated)
            allocate_overlap(storage);
        
        /* If we couldn't share another string then try to allocate from free space (avoiding holes) */
        if (storage->get_offset()==SgAsmGenericString::unallocated) {
            try {
                size_t need = storage->get_string().size() + 1;
                AddressIntervalSet::ConstIntervalIterator iter = get_freelist().bestFit(need,
                                                                                        get_freelist().intervals().begin());
                if (iter==get_freelist().intervals().end())
                    throw std::bad_alloc();
                ASSERT_require(iter->size() >= need);
                AddressInterval allocated = AddressInterval::baseSize(iter->least(), need);
                get_freelist().erase(allocated);
                rose_addr_t new_offset = allocated.least();
                storage->set_offset(new_offset);
            } catch(std::bad_alloc &x) {
                /* nothing large enough on the free list */
            }
        }

        /* If no free space area large enough then prepare to extend the section. */
        if (storage->get_offset()==SgAsmGenericString::unallocated) {
            extend_size += storage->get_string().size() + 1;
        }
    }

    /* If we were unable to allocate everything and there's still free space then it may be possible to reallocate all
     * strings in order to repack the table and avoid internal fragmentation. */
    //FIXME (RPM 2008-09-25)

    /* Change string table size as necessary. */
    if (extend_size>0) {
        /* The string table isn't large enough, so make it larger by extending the section that contains the table. The
         * containing section's "set_size" method should add the new space to the string table's free list. If our recursion
         * level is more than two calls deep then something went horribly wrong! */
        reallocated = true;
        container->get_file()->shift_extend(container, 0, extend_size);
        reallocate(false);
    } else if (shrink && get_freelist().size()>0) {
        /* See if we can release any address space and shrink the containing section. The containing section's "set_size"
         * method will adjust the free list by removing some bytes from it. */
        AddressIntervalSet::ConstIntervalIterator iter = get_freelist().intervals().end();
        ASSERT_forbid(iter == get_freelist().intervals().begin());
        --iter;
        AddressInterval hi = *iter;
        if (hi.least() + hi.size() == container->get_size())
            container->set_size(hi.least());
    }

    if (reallocated)
        set_isModified(true);
    return reallocated;
}

const AddressIntervalSet&
SgAsmGenericStrtab::get_freelist() const
{
    return p_freelist;
}

AddressIntervalSet&
SgAsmGenericStrtab::get_freelist()
{
    return p_freelist;
}

void
SgAsmGenericStrtab::dump(FILE *f, const char *prefix, ssize_t idx) const
{
    SgAsmGenericSection *container = get_container();

    char p[4096];
    if (idx>=0) {
        sprintf(p, "%sStrtab[%zd].", prefix, idx);
    } else {
        sprintf(p, "%sStrtab.", prefix);
    }
    int w = std::max(1, DUMP_FIELD_WIDTH-(int)strlen(p));
    
    if (container) {
        fprintf(f, "%s%-*s = [%d] \"%s\"\n", p, w, "container",
                container->get_id(), container->get_name()->get_string(true).c_str());
    } else {
        fprintf(f, "%s%-*s = <null>\n", p, w, "container");
    }

    fprintf(f, "%s%-*s =", p, w, "dont_free");
    for (size_t i=0; i<p_storage_list.size(); ++i) {
        if (p_storage_list[i] == p_dont_free)
            fprintf(f, " p_storage_list[%" PRIuPTR "]", i);
    }
    fputc('\n', f);
    
    fprintf(f, "%s%-*s = %" PRIuPTR " strings\n", p, w, "referenced", p_storage_list.size());
    for (size_t i=0; i<p_storage_list.size(); i++) {
        p_storage_list[i]->dump(f, p, i);
    }

    fprintf(f, "%s%-*s = %" PRIu64 " free regions\n", p, w, "freelist", get_freelist().size());
    BOOST_FOREACH (const AddressInterval &interval, get_freelist().intervals()) {
        fprintf(f, "%s%-*s = offset 0x%08" PRIx64 " (%" PRIu64 "),"
                " for 0x%08" PRIx64 " (%" PRIu64 ") byte%s,"
                " ending at 0x%08" PRIx64 " (%" PRIu64 ")\n",
                p, w, "",
                interval.least(), interval.least(),
                interval.size(), interval.size(), 1==interval.size()?"":"s",
                interval.greatest()+1, interval.greatest()+1);
    }
}

#endif
