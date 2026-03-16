/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/cspace.h -- Capability address space (radix tree of CNodes)
 *
 * Mirrors: spl/kernel/core/cspace.spl
 *
 * A capability address is a bitstring consumed level by level as the lookup
 * walks down the CNode tree.  This implementation supports a two-level tree
 * (root + one child level).
 */

#ifndef SIMPLE_OS_CSPACE_H
#define SIMPLE_OS_CSPACE_H

#include "common/types.h"
#include "kernel/core/capability_types.h"

/* ---- Constants --------------------------------------------------------- */

#define CNODE_BITS   8       /* Each CNode indexes 2^8 = 256 slots */
#define CNODE_SIZE   256
#define MAX_DEPTH    2       /* Maximum tree depth (root + one child) */

/* ---- CNode ------------------------------------------------------------- */

typedef struct {
    cap_slot_t slots[CNODE_SIZE];
    uint32_t   depth;        /* Level in the tree (0 = root) */
    uint32_t   guard;        /* Guard bits for path compression */
    uint32_t   guard_bits;   /* Number of significant guard bits */
    uint32_t   slot_count;   /* Number of occupied slots in this node */
} cnode_t;

/* ---- CSpace ------------------------------------------------------------ */

typedef struct {
    cnode_t  root;           /* Root CNode */
    uint32_t depth;          /* Total configured depth of the tree */
} cspace_t;

/* ---- API --------------------------------------------------------------- */

/* Create an empty CNode. */
void cnode_init(cnode_t *node, uint32_t depth, uint32_t guard,
                uint32_t guard_bits);

/* Create a fresh CSpace with an empty root CNode. */
void cspace_init(cspace_t *cs);

/* Lookup a capability by its full address.
 * Returns true and copies the slot to *out on success. */
bool cspace_lookup(const cspace_t *cs, uint32_t cap_addr, uint32_t depth,
                   cap_slot_t *out);

/* Insert a capability at a given address in the root CNode.
 * Returns true and sets *out_idx on success. */
bool cspace_insert(cspace_t *cs, uint32_t cap_addr, cap_slot_t slot,
                   uint32_t *out_idx);

/* Insert at a specific raw index (bypasses address decoding). */
bool cspace_insert_at(cspace_t *cs, uint32_t index, cap_slot_t slot);

/* Delete the capability at the given address in the root CNode. */
bool cspace_delete(cspace_t *cs, uint32_t cap_addr);

/* Delete at a specific raw index. */
bool cspace_delete_at(cspace_t *cs, uint32_t index);

/* Return the number of occupied slots. */
uint32_t cspace_count(const cspace_t *cs);

/* Return the number of free slots. */
uint32_t cspace_free_count(const cspace_t *cs);

#endif /* SIMPLE_OS_CSPACE_H */
