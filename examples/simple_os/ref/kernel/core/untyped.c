/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/untyped.c -- Untyped memory manager implementation
 *
 * Mirrors: spl/kernel/core/untyped.spl
 */

#include "kernel/core/untyped.h"

/* ---- Internal helpers -------------------------------------------------- */

static uint32_t align_up(uint32_t offset, uint32_t alignment)
{
    uint32_t mask = alignment - 1;
    return (offset + mask) & ~mask;
}

/* ------------------------------------------------------------------------ */

uint32_t kernel_object_size(kernel_object_type_t obj_type,
                            uint32_t size_bits)
{
    switch (obj_type) {
    case KERNEL_OBJ_ENDPOINT:     return UNTYPED_ENDPOINT_SIZE;
    case KERNEL_OBJ_NOTIFICATION: return UNTYPED_NOTIFICATION_SIZE;
    case KERNEL_OBJ_TCB:          return UNTYPED_TCB_SIZE;
    case KERNEL_OBJ_CNODE:
        /* CNode: 16 bytes per slot * (1 << size_bits) slots */
        return 16 * ((uint32_t)1 << size_bits);
    case KERNEL_OBJ_FRAME:        return UNTYPED_FRAME_OBJ_SIZE;
    case KERNEL_OBJ_PAGE_TABLE:   return UNTYPED_PAGE_TABLE_OBJ_SIZE;
    case KERNEL_OBJ_UNTYPED:      return (uint32_t)1 << size_bits;
    default:                      return 0;
    }
}

/* ---- API --------------------------------------------------------------- */

void untyped_init(untyped_t *ut, uint32_t base, uint32_t size_bits)
{
    ut->base_addr   = base;
    ut->size_bits   = size_bits;
    ut->total_size  = (uint32_t)1 << size_bits;
    ut->free_offset = 0;
    ut->child_count = 0;
    ut->is_device   = false;

    for (uint32_t i = 0; i < UNTYPED_MAX_CHILDREN; i++) {
        ut->children[i].obj_type = KERNEL_OBJ_ENDPOINT;
        ut->children[i].offset   = 0;
        ut->children[i].size     = 0;
        ut->children[i].active   = false;
    }
}

/* ------------------------------------------------------------------------ */

void untyped_init_device(untyped_t *ut, uint32_t base, uint32_t size_bits)
{
    untyped_init(ut, base, size_bits);
    ut->is_device = true;
}

/* ------------------------------------------------------------------------ */

bool untyped_retype(untyped_t *ut, kernel_object_type_t new_type,
                    uint32_t size_bits, uint32_t *out_addr)
{
    if (ut->child_count >= UNTYPED_MAX_CHILDREN) {
        return false;
    }

    uint32_t obj_size = kernel_object_size(new_type, size_bits);
    if (obj_size == 0) {
        return false;
    }

    /* Align the free pointer to the object's natural alignment */
    uint32_t aligned_offset = align_up(ut->free_offset, obj_size);

    /* Check space */
    if (aligned_offset + obj_size > ut->total_size) {
        return false;
    }

    /* Record the child */
    uint32_t child_idx = ut->child_count;
    ut->children[child_idx].obj_type = new_type;
    ut->children[child_idx].offset   = aligned_offset;
    ut->children[child_idx].size     = obj_size;
    ut->children[child_idx].active   = true;
    ut->child_count++;

    /* Advance bump pointer */
    ut->free_offset = aligned_offset + obj_size;

    /* Return physical address */
    *out_addr = ut->base_addr + aligned_offset;
    return true;
}

/* ------------------------------------------------------------------------ */

void untyped_revoke(untyped_t *ut)
{
    for (uint32_t i = 0; i < ut->child_count; i++) {
        ut->children[i].active = false;
    }
    ut->child_count = 0;
    ut->free_offset = 0;
}

/* ------------------------------------------------------------------------ */

void untyped_revoke_child(untyped_t *ut, uint32_t child_idx)
{
    if (child_idx >= ut->child_count) {
        return;
    }
    ut->children[child_idx].active = false;
}

/* ------------------------------------------------------------------------ */

uint32_t untyped_remaining(const untyped_t *ut)
{
    if (ut->free_offset >= ut->total_size) {
        return 0;
    }
    return ut->total_size - ut->free_offset;
}

/* ------------------------------------------------------------------------ */

uint32_t untyped_total_size(const untyped_t *ut)
{
    return ut->total_size;
}

/* ------------------------------------------------------------------------ */

uint32_t untyped_active_children(const untyped_t *ut)
{
    uint32_t count = 0;
    for (uint32_t i = 0; i < ut->child_count; i++) {
        if (ut->children[i].active) {
            count++;
        }
    }
    return count;
}

/* ------------------------------------------------------------------------ */

bool untyped_has_children(const untyped_t *ut)
{
    for (uint32_t i = 0; i < ut->child_count; i++) {
        if (ut->children[i].active) {
            return true;
        }
    }
    return false;
}

/* ------------------------------------------------------------------------ */

bool untyped_is_device(const untyped_t *ut)
{
    return ut->is_device;
}

/* ------------------------------------------------------------------------ */

uint32_t untyped_base(const untyped_t *ut)
{
    return ut->base_addr;
}

/* ------------------------------------------------------------------------ */

uint32_t untyped_size_bits_get(const untyped_t *ut)
{
    return ut->size_bits;
}

/* ------------------------------------------------------------------------ */

bool untyped_next_addr(const untyped_t *ut, kernel_object_type_t new_type,
                       uint32_t size_bits, uint32_t *out_addr)
{
    uint32_t obj_size = kernel_object_size(new_type, size_bits);
    if (obj_size == 0) {
        return false;
    }
    uint32_t aligned_offset = align_up(ut->free_offset, obj_size);
    if (aligned_offset + obj_size > ut->total_size) {
        return false;
    }
    *out_addr = ut->base_addr + aligned_offset;
    return true;
}
