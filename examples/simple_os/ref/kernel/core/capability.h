/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/capability.h -- Capability table (flat array of CapSlots)
 *
 * Mirrors: spl/kernel/core/capability.spl
 */

#ifndef SIMPLE_OS_CAPABILITY_H
#define SIMPLE_OS_CAPABILITY_H

#include "common/types.h"
#include "common/config.h"
#include "kernel/core/capability_types.h"

/* ---- Data structure ---------------------------------------------------- */

#define CAP_TABLE_MAX_SIZE  MAX_CAPS    /* 4096 */

typedef struct {
    cap_slot_t slots[CAP_TABLE_MAX_SIZE];
    uint32_t   size;        /* Allocated number of usable slots */
    uint32_t   count;       /* Number of occupied (non-Null) slots */
} cap_table_t;

/* ---- API --------------------------------------------------------------- */

/* Create an empty capability table with `size` usable slots. */
void cap_table_init(cap_table_t *table, uint32_t size);

/* Find the first empty slot. Returns true and sets *out_idx on success. */
bool cap_table_find_free(const cap_table_t *table, uint32_t *out_idx);

/* Insert a capability into the first available slot.
 * Returns true and sets *out_idx on success. */
bool cap_table_insert(cap_table_t *table, cap_type_t type_tag,
                      uint32_t object_ptr, cap_rights_t rights,
                      uint32_t *out_idx);

/* Insert a capability at a specific slot index.
 * Returns false if out of range or slot is occupied. */
bool cap_table_insert_at(cap_table_t *table, uint32_t index,
                         cap_type_t type_tag, uint32_t object_ptr,
                         cap_rights_t rights);

/* Lookup a capability by slot index.
 * Returns true and copies the slot to *out on success. */
bool cap_table_lookup(const cap_table_t *table, uint32_t index,
                      cap_slot_t *out);

/* Mint a derived capability with reduced rights and a badge.
 * Returns true and sets *out_idx on success. */
bool cap_table_mint(cap_table_t *table, uint32_t src_idx,
                    cap_rights_t new_rights, uint32_t badge,
                    uint32_t *out_idx);

/* Copy a capability preserving rights and badge.
 * Returns true and sets *out_idx on success. */
bool cap_table_copy(cap_table_t *table, uint32_t src_idx,
                    uint32_t *out_idx);

/* Revoke a capability and all derived capabilities (recursive). */
void cap_table_revoke(cap_table_t *table, uint32_t index);

/* Delete a single capability slot (derived caps become orphaned). */
void cap_table_delete(cap_table_t *table, uint32_t index);

/* Count capabilities referencing a given object pointer. */
uint32_t cap_table_ref_count(const cap_table_t *table, uint32_t object_ptr);

/* Check whether a slot has the required rights. */
bool cap_table_check_rights(const cap_table_t *table, uint32_t index,
                            cap_rights_t required);

#endif /* SIMPLE_OS_CAPABILITY_H */
