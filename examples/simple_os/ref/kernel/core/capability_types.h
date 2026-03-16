/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/capability_types.h -- Capability type definitions
 *
 * Mirrors: spl/kernel/core/capability_types.spl
 *
 * Capabilities are unforgeable tokens that grant authority over kernel objects.
 * Each capability carries a type tag, a pointer to the underlying kernel object,
 * a set of access rights, and an optional badge for endpoint discrimination.
 */

#ifndef SIMPLE_OS_CAPABILITY_TYPES_H
#define SIMPLE_OS_CAPABILITY_TYPES_H

#include "common/types.h"

/* ---- Capability object types ------------------------------------------- */

typedef enum {
    CAP_TYPE_NULL         = 0,   /* Empty / invalid slot */
    CAP_TYPE_UNTYPED      = 1,   /* Raw memory region */
    CAP_TYPE_ENDPOINT     = 2,   /* Synchronous IPC endpoint */
    CAP_TYPE_NOTIFICATION = 3,   /* Asynchronous notification word */
    CAP_TYPE_CNODE        = 4,   /* Capability node (CSpace tree node) */
    CAP_TYPE_TCB          = 5,   /* Thread control block */
    CAP_TYPE_FRAME        = 6,   /* Physical memory frame */
    CAP_TYPE_PAGE_TABLE   = 7,   /* Page table (second-level translation) */
    CAP_TYPE_PAGE_DIR     = 8,   /* Page directory (first-level translation) */
    CAP_TYPE_IRQ_CONTROL  = 9,   /* Global IRQ management authority */
    CAP_TYPE_IRQ_HANDLER  = 10,  /* Handler for a specific IRQ number */
    CAP_TYPE_SCHED_CONTEXT = 11, /* MCS scheduling context */
    CAP_TYPE_REPLY        = 12,  /* One-shot reply capability for IPC */
} cap_type_t;

/* ---- Capability rights bitmask ----------------------------------------- */

typedef struct {
    bool read;        /* Can read / receive through this capability */
    bool write;       /* Can write / send through this capability */
    bool grant;       /* Can copy (grant) this capability to another CSpace */
    bool revoke;      /* Can revoke all capabilities derived from this one */
} cap_rights_t;

/* ---- Capability slot --------------------------------------------------- */

typedef struct {
    cap_type_t   type_tag;      /* What kind of object this cap refers to */
    uint32_t     object_ptr;    /* Address / handle of the kernel object */
    cap_rights_t rights;        /* Access rights carried by this cap */
    uint32_t     badge;         /* Badge value (endpoint sender discrimination) */
    bool         is_derived;    /* True if minted / copied from another */
    uint32_t     parent_idx;    /* Index of parent cap (revocation tree) */
} cap_slot_t;

/* ---- Helper functions -------------------------------------------------- */

/* Create an empty (Null) capability slot. */
static inline cap_slot_t cap_slot_empty(void)
{
    cap_slot_t slot;
    slot.type_tag   = CAP_TYPE_NULL;
    slot.object_ptr = 0;
    slot.rights.read   = false;
    slot.rights.write  = false;
    slot.rights.grant  = false;
    slot.rights.revoke = false;
    slot.badge      = 0;
    slot.is_derived = false;
    slot.parent_idx = 0;
    return slot;
}

/* Returns true when the slot holds a valid (non-Null) capability. */
static inline bool cap_slot_is_valid(const cap_slot_t *slot)
{
    return slot->type_tag != CAP_TYPE_NULL;
}

/* Full rights -- used when the kernel initially creates an object capability. */
static inline cap_rights_t cap_rights_all(void)
{
    cap_rights_t r;
    r.read   = true;
    r.write  = true;
    r.grant  = true;
    r.revoke = true;
    return r;
}

/* Read-only rights. */
static inline cap_rights_t cap_rights_read_only(void)
{
    cap_rights_t r;
    r.read   = true;
    r.write  = false;
    r.grant  = false;
    r.revoke = false;
    return r;
}

/* Write-only rights. */
static inline cap_rights_t cap_rights_write_only(void)
{
    cap_rights_t r;
    r.read   = false;
    r.write  = true;
    r.grant  = false;
    r.revoke = false;
    return r;
}

/* Read-write without grant or revoke. */
static inline cap_rights_t cap_rights_read_write(void)
{
    cap_rights_t r;
    r.read   = true;
    r.write  = true;
    r.grant  = false;
    r.revoke = false;
    return r;
}

/* Compute the intersection of two rights sets (monotonic decrease). */
static inline cap_rights_t cap_rights_mask(cap_rights_t original,
                                           cap_rights_t mask)
{
    cap_rights_t r;
    r.read   = original.read   && mask.read;
    r.write  = original.write  && mask.write;
    r.grant  = original.grant  && mask.grant;
    r.revoke = original.revoke && mask.revoke;
    return r;
}

/* Check whether `inner` is a subset of `outer`. */
static inline bool cap_rights_is_subset(cap_rights_t inner,
                                        cap_rights_t outer)
{
    if (inner.read   && !outer.read)   return false;
    if (inner.write  && !outer.write)  return false;
    if (inner.grant  && !outer.grant)  return false;
    if (inner.revoke && !outer.revoke) return false;
    return true;
}

/* Check whether two rights sets are identical. */
static inline bool cap_rights_equal(cap_rights_t a, cap_rights_t b)
{
    return (a.read == b.read && a.write == b.write &&
            a.grant == b.grant && a.revoke == b.revoke);
}

/* Create a capability slot for a kernel object with full rights. */
static inline cap_slot_t cap_slot_create(cap_type_t type_tag,
                                         uint32_t object_ptr)
{
    cap_slot_t slot;
    slot.type_tag   = type_tag;
    slot.object_ptr = object_ptr;
    slot.rights     = cap_rights_all();
    slot.badge      = 0;
    slot.is_derived = false;
    slot.parent_idx = 0;
    return slot;
}

/* Create a badged variant of a slot (endpoint discrimination). */
static inline cap_slot_t cap_slot_badge(cap_slot_t slot, uint32_t badge)
{
    cap_slot_t badged = slot;
    badged.badge = badge;
    return badged;
}

#endif /* SIMPLE_OS_CAPABILITY_TYPES_H */
