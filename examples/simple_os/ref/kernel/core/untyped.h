/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/untyped.h -- Untyped memory manager (seL4-style)
 *
 * Mirrors: spl/kernel/core/untyped.spl
 *
 * An UntypedMemory object represents a contiguous region of physical memory
 * that has not yet been given a type.  Objects are allocated sequentially
 * (bump allocator) within the region.
 */

#ifndef SIMPLE_OS_UNTYPED_H
#define SIMPLE_OS_UNTYPED_H

#include "common/types.h"

/* ---- Object type tags for retype --------------------------------------- */

typedef enum {
    KERNEL_OBJ_ENDPOINT     = 0,
    KERNEL_OBJ_NOTIFICATION = 1,
    KERNEL_OBJ_TCB          = 2,
    KERNEL_OBJ_CNODE        = 3,
    KERNEL_OBJ_FRAME        = 4,
    KERNEL_OBJ_PAGE_TABLE   = 5,
    KERNEL_OBJ_UNTYPED      = 6,
} kernel_object_type_t;

/* ---- Object size constants (bytes, powers of two) ---------------------- */

#define UNTYPED_ENDPOINT_SIZE       64
#define UNTYPED_NOTIFICATION_SIZE   64
#define UNTYPED_TCB_SIZE            1024
#define UNTYPED_FRAME_OBJ_SIZE      4096
#define UNTYPED_PAGE_TABLE_OBJ_SIZE 4096
#define UNTYPED_MAX_CHILDREN        256

/* ---- Child object descriptor ------------------------------------------- */

typedef struct {
    kernel_object_type_t obj_type;
    uint32_t             offset;     /* Offset from base_addr */
    uint32_t             size;       /* Size in bytes */
    bool                 active;
} untyped_child_t;

/* ---- UntypedMemory ----------------------------------------------------- */

typedef struct {
    uint32_t         base_addr;      /* Physical base (naturally aligned) */
    uint32_t         size_bits;      /* log2 of total size */
    uint32_t         total_size;     /* 1 << size_bits */
    uint32_t         free_offset;    /* Bump pointer */
    untyped_child_t  children[UNTYPED_MAX_CHILDREN];
    uint32_t         child_count;
    bool             is_device;      /* Device memory (non-cacheable) */
} untyped_t;

/* ---- API --------------------------------------------------------------- */

/* Create an untyped memory region. base must be aligned to (1 << size_bits). */
void untyped_init(untyped_t *ut, uint32_t base, uint32_t size_bits);

/* Create an untyped for device memory. */
void untyped_init_device(untyped_t *ut, uint32_t base, uint32_t size_bits);

/* Get the size of a kernel object type. */
uint32_t kernel_object_size(kernel_object_type_t obj_type,
                            uint32_t size_bits);

/* Retype: carve a typed object.
 * Returns true and sets *out_addr on success. */
bool untyped_retype(untyped_t *ut, kernel_object_type_t new_type,
                    uint32_t size_bits, uint32_t *out_addr);

/* Revoke all children and reclaim the entire region. */
void untyped_revoke(untyped_t *ut);

/* Revoke a single child by index. */
void untyped_revoke_child(untyped_t *ut, uint32_t child_idx);

/* Remaining free bytes. */
uint32_t untyped_remaining(const untyped_t *ut);

/* Total size. */
uint32_t untyped_total_size(const untyped_t *ut);

/* Number of active children. */
uint32_t untyped_active_children(const untyped_t *ut);

/* Check if any active children exist. */
bool untyped_has_children(const untyped_t *ut);

/* Check if device memory. */
bool untyped_is_device(const untyped_t *ut);

/* Get base address. */
uint32_t untyped_base(const untyped_t *ut);

/* Get size_bits. */
uint32_t untyped_size_bits_get(const untyped_t *ut);

/* Get the physical address the next retype would use.
 * Returns true and sets *out_addr on success. */
bool untyped_next_addr(const untyped_t *ut, kernel_object_type_t new_type,
                       uint32_t size_bits, uint32_t *out_addr);

#endif /* SIMPLE_OS_UNTYPED_H */
