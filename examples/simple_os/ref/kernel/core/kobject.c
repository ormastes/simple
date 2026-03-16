/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/kobject.c -- Kernel object wrapper implementation
 *
 * Mirrors: spl/kernel/core/kobject.spl
 */

#include "kernel/core/kobject.h"

/* ------------------------------------------------------------------------ */

kobject_t kobject_create(kobject_type_t obj_type, uint32_t addr,
                         uint32_t size_bits)
{
    kobject_t obj;
    obj.obj_type   = obj_type;
    obj.ref_count  = 1;
    obj.size_bits  = size_bits;
    obj.parent_ptr = 0;
    obj.addr       = addr;
    obj.is_alive   = true;
    return obj;
}

/* ------------------------------------------------------------------------ */

kobject_t kobject_create_from(kobject_type_t obj_type, uint32_t addr,
                              uint32_t size_bits, uint32_t parent_ptr)
{
    kobject_t obj;
    obj.obj_type   = obj_type;
    obj.ref_count  = 1;
    obj.size_bits  = size_bits;
    obj.parent_ptr = parent_ptr;
    obj.addr       = addr;
    obj.is_alive   = true;
    return obj;
}

/* ------------------------------------------------------------------------ */

void kobject_retain(kobject_t *obj)
{
    obj->ref_count++;
}

/* ------------------------------------------------------------------------ */

bool kobject_release(kobject_t *obj)
{
    if (obj->ref_count == 0) {
        return true;
    }
    obj->ref_count--;
    if (obj->ref_count == 0) {
        obj->is_alive = false;
        return true;
    }
    return false;
}

/* ------------------------------------------------------------------------ */

uint32_t kobject_size(const kobject_t *obj)
{
    return (uint32_t)1 << obj->size_bits;
}

/* ------------------------------------------------------------------------ */

cap_type_t kobject_to_cap_type(kobject_type_t obj_type)
{
    switch (obj_type) {
    case KOBJECT_TYPE_UNTYPED:       return CAP_TYPE_UNTYPED;
    case KOBJECT_TYPE_ENDPOINT:      return CAP_TYPE_ENDPOINT;
    case KOBJECT_TYPE_NOTIFICATION:  return CAP_TYPE_NOTIFICATION;
    case KOBJECT_TYPE_CNODE:         return CAP_TYPE_CNODE;
    case KOBJECT_TYPE_TCB:           return CAP_TYPE_TCB;
    case KOBJECT_TYPE_FRAME:         return CAP_TYPE_FRAME;
    case KOBJECT_TYPE_PAGE_TABLE:    return CAP_TYPE_PAGE_TABLE;
    case KOBJECT_TYPE_PAGE_DIR:      return CAP_TYPE_PAGE_DIR;
    case KOBJECT_TYPE_SCHED_CONTEXT: return CAP_TYPE_SCHED_CONTEXT;
    default:                         return CAP_TYPE_NULL;
    }
}

/* ------------------------------------------------------------------------ */

void kobject_pool_init(kobject_pool_t *pool)
{
    pool->count = 0;
    for (uint32_t i = 0; i < KOBJECT_POOL_SIZE; i++) {
        pool->objects[i].obj_type   = KOBJECT_TYPE_UNTYPED;
        pool->objects[i].ref_count  = 0;
        pool->objects[i].size_bits  = 0;
        pool->objects[i].parent_ptr = 0;
        pool->objects[i].addr       = 0;
        pool->objects[i].is_alive   = false;
    }
}

/* ------------------------------------------------------------------------ */

bool kobject_pool_alloc(kobject_pool_t *pool, kobject_type_t obj_type,
                        uint32_t addr, uint32_t size_bits,
                        uint32_t *out_idx)
{
    if (pool->count >= KOBJECT_POOL_SIZE) {
        return false;
    }

    for (uint32_t i = 0; i < KOBJECT_POOL_SIZE; i++) {
        if (!pool->objects[i].is_alive && pool->objects[i].ref_count == 0) {
            pool->objects[i] = kobject_create(obj_type, addr, size_bits);
            pool->count++;
            *out_idx = i;
            return true;
        }
    }

    return false;
}

/* ------------------------------------------------------------------------ */

bool kobject_pool_get(const kobject_pool_t *pool, uint32_t index,
                      kobject_t *out)
{
    if (index >= KOBJECT_POOL_SIZE) {
        return false;
    }
    if (!pool->objects[index].is_alive) {
        return false;
    }
    *out = pool->objects[index];
    return true;
}

/* ------------------------------------------------------------------------ */

bool kobject_pool_release(kobject_pool_t *pool, uint32_t index)
{
    if (index >= KOBJECT_POOL_SIZE) {
        return false;
    }
    if (!pool->objects[index].is_alive) {
        return false;
    }
    bool freed = kobject_release(&pool->objects[index]);
    if (freed) {
        pool->count--;
    }
    return freed;
}
