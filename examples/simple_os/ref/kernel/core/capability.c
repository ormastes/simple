/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/capability.c -- Capability table implementation
 *
 * Mirrors: spl/kernel/core/capability.spl
 */

#include "kernel/core/capability.h"

/* ------------------------------------------------------------------------ */

void cap_table_init(cap_table_t *table, uint32_t size)
{
    uint32_t capped = size;
    if (capped > CAP_TABLE_MAX_SIZE) {
        capped = CAP_TABLE_MAX_SIZE;
    }

    table->size  = capped;
    table->count = 0;

    for (uint32_t i = 0; i < CAP_TABLE_MAX_SIZE; i++) {
        table->slots[i] = cap_slot_empty();
    }
}

/* ------------------------------------------------------------------------ */

bool cap_table_find_free(const cap_table_t *table, uint32_t *out_idx)
{
    for (uint32_t i = 0; i < table->size; i++) {
        if (table->slots[i].type_tag == CAP_TYPE_NULL) {
            *out_idx = i;
            return true;
        }
    }
    return false;
}

/* ------------------------------------------------------------------------ */

bool cap_table_insert(cap_table_t *table, cap_type_t type_tag,
                      uint32_t object_ptr, cap_rights_t rights,
                      uint32_t *out_idx)
{
    if (table->count >= table->size) {
        return false;
    }

    uint32_t idx = 0;
    bool found = false;
    for (uint32_t i = 0; i < table->size; i++) {
        if (table->slots[i].type_tag == CAP_TYPE_NULL) {
            idx = i;
            found = true;
            break;
        }
    }

    if (!found) {
        return false;
    }

    table->slots[idx].type_tag   = type_tag;
    table->slots[idx].object_ptr = object_ptr;
    table->slots[idx].rights     = rights;
    table->slots[idx].badge      = 0;
    table->slots[idx].is_derived = false;
    table->slots[idx].parent_idx = 0;

    table->count++;
    *out_idx = idx;
    return true;
}

/* ------------------------------------------------------------------------ */

bool cap_table_insert_at(cap_table_t *table, uint32_t index,
                         cap_type_t type_tag, uint32_t object_ptr,
                         cap_rights_t rights)
{
    if (index >= table->size) {
        return false;
    }
    if (table->slots[index].type_tag != CAP_TYPE_NULL) {
        return false;
    }

    table->slots[index].type_tag   = type_tag;
    table->slots[index].object_ptr = object_ptr;
    table->slots[index].rights     = rights;
    table->slots[index].badge      = 0;
    table->slots[index].is_derived = false;
    table->slots[index].parent_idx = 0;

    table->count++;
    return true;
}

/* ------------------------------------------------------------------------ */

bool cap_table_lookup(const cap_table_t *table, uint32_t index,
                      cap_slot_t *out)
{
    if (index >= table->size) {
        return false;
    }
    if (table->slots[index].type_tag == CAP_TYPE_NULL) {
        return false;
    }
    *out = table->slots[index];
    return true;
}

/* ------------------------------------------------------------------------ */

bool cap_table_mint(cap_table_t *table, uint32_t src_idx,
                    cap_rights_t new_rights, uint32_t badge,
                    uint32_t *out_idx)
{
    /* Validate source */
    if (src_idx >= table->size) {
        return false;
    }
    if (table->slots[src_idx].type_tag == CAP_TYPE_NULL) {
        return false;
    }

    /* Source must carry grant rights */
    if (!table->slots[src_idx].rights.grant) {
        return false;
    }

    cap_slot_t src = table->slots[src_idx];

    /* Mask new_rights against the source rights (monotonic decrease) */
    cap_rights_t masked = cap_rights_mask(src.rights, new_rights);

    /* Find a free slot */
    uint32_t dst_idx = 0;
    bool found = false;
    for (uint32_t i = 0; i < table->size; i++) {
        if (table->slots[i].type_tag == CAP_TYPE_NULL) {
            dst_idx = i;
            found = true;
            break;
        }
    }

    if (!found) {
        return false;
    }

    table->slots[dst_idx].type_tag   = src.type_tag;
    table->slots[dst_idx].object_ptr = src.object_ptr;
    table->slots[dst_idx].rights     = masked;
    table->slots[dst_idx].badge      = badge;
    table->slots[dst_idx].is_derived = true;
    table->slots[dst_idx].parent_idx = src_idx;

    table->count++;
    *out_idx = dst_idx;
    return true;
}

/* ------------------------------------------------------------------------ */

bool cap_table_copy(cap_table_t *table, uint32_t src_idx,
                    uint32_t *out_idx)
{
    if (src_idx >= table->size) {
        return false;
    }
    if (table->slots[src_idx].type_tag == CAP_TYPE_NULL) {
        return false;
    }
    if (!table->slots[src_idx].rights.grant) {
        return false;
    }

    cap_slot_t src = table->slots[src_idx];

    uint32_t dst_idx = 0;
    bool found = false;
    for (uint32_t i = 0; i < table->size; i++) {
        if (table->slots[i].type_tag == CAP_TYPE_NULL) {
            dst_idx = i;
            found = true;
            break;
        }
    }

    if (!found) {
        return false;
    }

    table->slots[dst_idx].type_tag   = src.type_tag;
    table->slots[dst_idx].object_ptr = src.object_ptr;
    table->slots[dst_idx].rights     = src.rights;
    table->slots[dst_idx].badge      = src.badge;
    table->slots[dst_idx].is_derived = true;
    table->slots[dst_idx].parent_idx = src_idx;

    table->count++;
    *out_idx = dst_idx;
    return true;
}

/* ------------------------------------------------------------------------ */

void cap_table_revoke(cap_table_t *table, uint32_t index)
{
    if (index >= table->size) {
        return;
    }
    if (table->slots[index].type_tag == CAP_TYPE_NULL) {
        return;
    }

    /* Recursively revoke all children that list `index` as parent */
    for (uint32_t i = 0; i < table->size; i++) {
        if (i == index) {
            continue;
        }
        if (table->slots[i].type_tag == CAP_TYPE_NULL) {
            continue;
        }
        if (table->slots[i].is_derived &&
            table->slots[i].parent_idx == index) {
            cap_table_revoke(table, i);
        }
    }

    /* Delete the slot itself */
    table->slots[index] = cap_slot_empty();
    table->count--;
}

/* ------------------------------------------------------------------------ */

void cap_table_delete(cap_table_t *table, uint32_t index)
{
    if (index >= table->size) {
        return;
    }
    if (table->slots[index].type_tag == CAP_TYPE_NULL) {
        return;
    }
    table->slots[index] = cap_slot_empty();
    table->count--;
}

/* ------------------------------------------------------------------------ */

uint32_t cap_table_ref_count(const cap_table_t *table, uint32_t object_ptr)
{
    uint32_t count = 0;
    for (uint32_t i = 0; i < table->size; i++) {
        if (table->slots[i].type_tag != CAP_TYPE_NULL) {
            if (table->slots[i].object_ptr == object_ptr) {
                count++;
            }
        }
    }
    return count;
}

/* ------------------------------------------------------------------------ */

bool cap_table_check_rights(const cap_table_t *table, uint32_t index,
                            cap_rights_t required)
{
    if (index >= table->size) {
        return false;
    }
    if (table->slots[index].type_tag == CAP_TYPE_NULL) {
        return false;
    }
    return cap_rights_is_subset(required, table->slots[index].rights);
}
