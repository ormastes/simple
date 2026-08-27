#ifndef SIMPLEOS_BAREMETAL_BUMP_HEAP_H
#define SIMPLEOS_BAREMETAL_BUMP_HEAP_H

/* Fixed boot heaps must reject arithmetic overflow before g_heap_off changes:
 * runtime-derived sizes are untrusted at this boundary. */
static inline int rv_size_add(size_t left, size_t right, size_t *out){
    if (left > (size_t)-1 - right) return 0;
    *out = left + right;
    return 1;
}

static inline int rv_size_mul(size_t left, size_t right, size_t *out){
    if (left != 0 && right > (size_t)-1 / left) return 0;
    *out = left * right;
    return 1;
}

static inline int rv_size_align16(size_t size, size_t *out){
    size_t expanded = 0;
    if (!rv_size_add(size, 15U, &expanded)) return 0;
    *out = expanded & ~(size_t)15U;
    return 1;
}

static void *rv_alloc(size_t size){
    size_t aligned = 0;
    if (!rv_size_align16(size, &aligned)) return 0;
    if (g_heap_off > sizeof(g_heap)) return 0;
    if (aligned > sizeof(g_heap) - g_heap_off) return 0;
    void *p = &g_heap[g_heap_off];
    g_heap_off += aligned;
    return p;
}

static inline void *rv_calloc(size_t count, size_t size){
    size_t total = 0;
    if (!rv_size_mul(count, size, &total)) return 0;
    unsigned char *p = (unsigned char *)rv_alloc(total);
    if (!p) return 0;
    for (size_t i = 0; i < total; ++i) p[i] = 0;
    return p;
}

/* This bump allocator records no allocation extent, so copying an arbitrary
 * requested `realloc` size would read beyond the old object. Preserve the
 * standard allocation-only NULL form; reject moving an existing allocation
 * until an extent-owning allocator is introduced. */
static inline void *rv_realloc(void *ptr, size_t size){
    if (ptr != 0) return 0;
    return rv_alloc(size);
}

#ifdef BAREMETAL_ENABLE_ALIGNED_ALLOC
static void *rv_alloc_aligned(size_t size, size_t align){
    if (align == 0) align = 16U;
    size_t offset = g_heap_off;
    if (offset > sizeof(g_heap)) return 0;
    size_t rem = offset % align;
    if (rem != 0 && !rv_size_add(offset, align - rem, &offset)) return 0;
    size_t aligned = 0;
    if (!rv_size_align16(size, &aligned)) return 0;
    if (offset > sizeof(g_heap)) return 0;
    if (aligned > sizeof(g_heap) - offset) return 0;
    void *p = &g_heap[offset];
    g_heap_off = offset + aligned;
    return p;
}
#endif

#endif
