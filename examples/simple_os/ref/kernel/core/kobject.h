/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/kobject.h -- Kernel object wrapper (tagged union)
 *
 * Mirrors: spl/kernel/core/kobject.spl
 *
 * Every resource managed by the microkernel is represented as a KObject.
 * Capabilities point to KObjects; the reference count tracks how many
 * capabilities reference a given object so the kernel knows when it is
 * safe to reclaim the underlying memory.
 */

#ifndef SIMPLE_OS_KOBJECT_H
#define SIMPLE_OS_KOBJECT_H

#include "common/types.h"
#include "kernel/core/capability_types.h"

/* ---- Kernel object type ------------------------------------------------ */

typedef enum {
    KOBJECT_TYPE_UNTYPED      = 0,
    KOBJECT_TYPE_ENDPOINT     = 1,
    KOBJECT_TYPE_NOTIFICATION = 2,
    KOBJECT_TYPE_CNODE        = 3,
    KOBJECT_TYPE_TCB          = 4,
    KOBJECT_TYPE_FRAME        = 5,
    KOBJECT_TYPE_PAGE_TABLE   = 6,
    KOBJECT_TYPE_PAGE_DIR     = 7,
    KOBJECT_TYPE_SCHED_CONTEXT = 8,
} kobject_type_t;

/* ---- KObject header ---------------------------------------------------- */

#define KOBJECT_POOL_SIZE  1024

typedef struct {
    kobject_type_t obj_type;
    uint32_t       ref_count;    /* Number of capabilities pointing here */
    uint32_t       size_bits;    /* log2 of the object size in bytes */
    uint32_t       parent_ptr;   /* Address of parent untyped (0 = root) */
    uint32_t       addr;         /* Base address in physical memory */
    bool           is_alive;
} kobject_t;

/* ---- KObject pool ------------------------------------------------------ */

typedef struct {
    kobject_t objects[KOBJECT_POOL_SIZE];
    uint32_t  count;
} kobject_pool_t;

/* ---- API --------------------------------------------------------------- */

/* Create a single kernel object descriptor (ref_count starts at 1). */
kobject_t kobject_create(kobject_type_t obj_type, uint32_t addr,
                         uint32_t size_bits);

/* Create a kernel object retyped from a parent untyped region. */
kobject_t kobject_create_from(kobject_type_t obj_type, uint32_t addr,
                              uint32_t size_bits, uint32_t parent_ptr);

/* Increment reference count. */
void kobject_retain(kobject_t *obj);

/* Decrement reference count. Returns true when count reaches zero. */
bool kobject_release(kobject_t *obj);

/* Compute size in bytes from size_bits. */
uint32_t kobject_size(const kobject_t *obj);

/* Map KObjectType to CapType for capability creation. */
cap_type_t kobject_to_cap_type(kobject_type_t obj_type);

/* Pool operations */
void kobject_pool_init(kobject_pool_t *pool);
bool kobject_pool_alloc(kobject_pool_t *pool, kobject_type_t obj_type,
                        uint32_t addr, uint32_t size_bits,
                        uint32_t *out_idx);
bool kobject_pool_get(const kobject_pool_t *pool, uint32_t index,
                      kobject_t *out);
bool kobject_pool_release(kobject_pool_t *pool, uint32_t index);

#endif /* SIMPLE_OS_KOBJECT_H */
