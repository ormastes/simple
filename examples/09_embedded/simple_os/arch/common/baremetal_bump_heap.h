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

/* Heap extent. By default the arena is the includer's own `g_heap` array, which
 * is what every existing caller of this header expects. A TU whose linker
 * script already RESERVES a heap region (riscv64's linker_riscv_common.ld
 * reserves 64 MB between __heap_start and __heap_end, documented there as "for
 * bump allocator") defines RV_HEAP_BASE/RV_HEAP_SIZE to point at it instead, so
 * that reservation stops being dead address space. Nothing else in this header
 * changes: same bump discipline, same overflow rejection, same NULL-on-full. */
#ifndef RV_HEAP_BASE
#define RV_HEAP_BASE  (g_heap)
#endif
#ifndef RV_HEAP_SIZE
#define RV_HEAP_SIZE  (sizeof(g_heap))
#endif

/* Exhaustion must NAME itself, at the single funnel every caller passes
 * through. Reporting it in malloc() only was fail-open: rt_alloc/calloc and
 * every in-TU `rv_alloc(...)` call site bypass malloc entirely, so a full arena
 * returned NULL, the caller stored through it, and the only evidence was a
 * store fault at an unattributable address -- which is exactly how the riscv64
 * build-and-run row's failure read. A TU that can print defines
 * RV_HEAP_EXHAUSTED_REPORT(); the default is a no-op, so no other includer of
 * this header changes behaviour. The report does NOT change the return value:
 * callers still see NULL and fail exactly as before. */
#ifndef RV_HEAP_EXHAUSTED_REPORT
#define RV_HEAP_EXHAUSTED_REPORT() ((void)0)
#endif

/* Optional coarse progress hook: lets a TU that can print show HOW the arena
 * is being consumed (steady vs runaway) instead of only that it ran out.
 * Default no-op. */
#ifndef RV_HEAP_PROGRESS
#define RV_HEAP_PROGRESS(off) ((void)(off))
#endif

static void *rv_alloc(size_t size){
    size_t aligned = 0;
    if (!rv_size_align16(size, &aligned)) { RV_HEAP_EXHAUSTED_REPORT(); return 0; }
    if (g_heap_off > (size_t)RV_HEAP_SIZE) { RV_HEAP_EXHAUSTED_REPORT(); return 0; }
    if (aligned > (size_t)RV_HEAP_SIZE - g_heap_off) { RV_HEAP_EXHAUSTED_REPORT(); return 0; }
    void *p = &(RV_HEAP_BASE)[g_heap_off];
    g_heap_off += aligned;
    RV_HEAP_PROGRESS(g_heap_off);
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
    if (offset > (size_t)RV_HEAP_SIZE) { RV_HEAP_EXHAUSTED_REPORT(); return 0; }
    size_t rem = offset % align;
    if (rem != 0 && !rv_size_add(offset, align - rem, &offset)) { RV_HEAP_EXHAUSTED_REPORT(); return 0; }
    size_t aligned = 0;
    if (!rv_size_align16(size, &aligned)) { RV_HEAP_EXHAUSTED_REPORT(); return 0; }
    if (offset > (size_t)RV_HEAP_SIZE) { RV_HEAP_EXHAUSTED_REPORT(); return 0; }
    if (aligned > (size_t)RV_HEAP_SIZE - offset) { RV_HEAP_EXHAUSTED_REPORT(); return 0; }
    void *p = &(RV_HEAP_BASE)[offset];
    g_heap_off = offset + aligned;
    return p;
}
#endif

#endif
