/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/cspace.c -- Capability address space implementation
 *
 * Mirrors: spl/kernel/core/cspace.spl
 */

#include "kernel/core/cspace.h"

/* ---- Internal helpers -------------------------------------------------- */

/* Extract `num_bits` bits from `addr` starting at bit position `offset`.
 * Bit 0 is the most-significant consumed bit. */
static uint32_t extract_bits(uint32_t addr, uint32_t offset,
                             uint32_t num_bits)
{
    if (num_bits == 0) {
        return 0;
    }
    uint32_t shift = 32 - offset - num_bits;
    uint32_t mask  = ((uint32_t)1 << num_bits) - 1;
    return (addr >> shift) & mask;
}

/* Check whether the guard at a CNode matches the corresponding bits. */
static bool guard_matches(const cnode_t *node, uint32_t addr,
                          uint32_t bit_offset)
{
    if (node->guard_bits == 0) {
        return true;
    }
    uint32_t extracted = extract_bits(addr, bit_offset, node->guard_bits);
    return extracted == node->guard;
}

/* ---- API --------------------------------------------------------------- */

void cnode_init(cnode_t *node, uint32_t depth, uint32_t guard,
                uint32_t guard_bits)
{
    for (uint32_t i = 0; i < CNODE_SIZE; i++) {
        node->slots[i] = cap_slot_empty();
    }
    node->depth      = depth;
    node->guard      = guard;
    node->guard_bits = guard_bits;
    node->slot_count = 0;
}

/* ------------------------------------------------------------------------ */

void cspace_init(cspace_t *cs)
{
    cnode_init(&cs->root, 0, 0, 0);
    cs->depth = 1;
}

/* ------------------------------------------------------------------------ */

bool cspace_lookup(const cspace_t *cs, uint32_t cap_addr, uint32_t depth,
                   cap_slot_t *out)
{
    uint32_t resolve_depth = depth;
    if (resolve_depth > MAX_DEPTH) {
        resolve_depth = MAX_DEPTH;
    }
    if (resolve_depth == 0) {
        return false;
    }

    /* Level 0: root CNode */
    uint32_t bit_offset = 0;

    if (!guard_matches(&cs->root, cap_addr, bit_offset)) {
        return false;
    }
    bit_offset += cs->root.guard_bits;

    uint32_t root_index = extract_bits(cap_addr, bit_offset, CNODE_BITS);
    bit_offset += CNODE_BITS;

    if (root_index >= CNODE_SIZE) {
        return false;
    }

    const cap_slot_t *root_slot = &cs->root.slots[root_index];

    if (resolve_depth == 1) {
        if (root_slot->type_tag == CAP_TYPE_NULL) {
            return false;
        }
        *out = *root_slot;
        return true;
    }

    /* For depth >= 2, return what we found at root level.
     * A full implementation would dereference the CNode object_ptr. */
    if (root_slot->type_tag == CAP_TYPE_NULL) {
        return false;
    }
    *out = *root_slot;
    return true;
}

/* ------------------------------------------------------------------------ */

bool cspace_insert(cspace_t *cs, uint32_t cap_addr, cap_slot_t slot,
                   uint32_t *out_idx)
{
    uint32_t bit_offset = 0;

    if (!guard_matches(&cs->root, cap_addr, bit_offset)) {
        return false;
    }
    bit_offset += cs->root.guard_bits;

    uint32_t index = extract_bits(cap_addr, bit_offset, CNODE_BITS);

    if (index >= CNODE_SIZE) {
        return false;
    }

    if (cs->root.slots[index].type_tag != CAP_TYPE_NULL) {
        return false;
    }

    cs->root.slots[index] = slot;
    cs->root.slot_count++;
    *out_idx = index;
    return true;
}

/* ------------------------------------------------------------------------ */

bool cspace_insert_at(cspace_t *cs, uint32_t index, cap_slot_t slot)
{
    if (index >= CNODE_SIZE) {
        return false;
    }
    if (cs->root.slots[index].type_tag != CAP_TYPE_NULL) {
        return false;
    }

    cs->root.slots[index] = slot;
    cs->root.slot_count++;
    return true;
}

/* ------------------------------------------------------------------------ */

bool cspace_delete(cspace_t *cs, uint32_t cap_addr)
{
    uint32_t bit_offset = 0;

    if (!guard_matches(&cs->root, cap_addr, bit_offset)) {
        return false;
    }
    bit_offset += cs->root.guard_bits;

    uint32_t index = extract_bits(cap_addr, bit_offset, CNODE_BITS);

    if (index >= CNODE_SIZE) {
        return false;
    }
    if (cs->root.slots[index].type_tag == CAP_TYPE_NULL) {
        return false;
    }

    cs->root.slots[index] = cap_slot_empty();
    cs->root.slot_count--;
    return true;
}

/* ------------------------------------------------------------------------ */

bool cspace_delete_at(cspace_t *cs, uint32_t index)
{
    if (index >= CNODE_SIZE) {
        return false;
    }
    if (cs->root.slots[index].type_tag == CAP_TYPE_NULL) {
        return false;
    }

    cs->root.slots[index] = cap_slot_empty();
    cs->root.slot_count--;
    return true;
}

/* ------------------------------------------------------------------------ */

uint32_t cspace_count(const cspace_t *cs)
{
    return cs->root.slot_count;
}

/* ------------------------------------------------------------------------ */

uint32_t cspace_free_count(const cspace_t *cs)
{
    return CNODE_SIZE - cs->root.slot_count;
}
