/*
 * Sampled guard-page allocator (plan M2, native-C mirror).
 *
 * Mirrors src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs:
 * GWP-ASan-style 1-in-N sampling. A sampled allocation lands on its own
 * mmap'd slot with mprotect(PROT_NONE) leading/trailing guard pages and a
 * right-aligned user pointer, so a small overflow SIGSEGVs on the guard
 * page instead of corrupting a neighbor. Freeing a sampled slot does not
 * munmap immediately -- it PROT_NONEs the whole slot (data pages too, so a
 * use-after-free also traps) and defers the real munmap to a bounded FIFO
 * ring. See doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md
 * and doc/08_tracking/bug/mem_infra_guard_row_false_on_native_backends_2026-07-31.md
 * (the bug this closes: native `rt_alloc` never had a guard-page mechanism).
 *
 * This header is #include'd (not linked) by BOTH runtime_memory.c (the
 * "hosted"/cranelift-JIT rt_alloc, resolved via dlsym) and runtime_native.c
 * (the native-build/AOT rt_alloc, statically linked as part of the
 * core-c-bootstrap runtime bundle) -- those two files already define
 * duplicate rt_alloc/rt_free symbols tolerated via first-definition-wins
 * linking (see the bug doc above), so every symbol here is `static`
 * (internal linkage): each translation unit gets its own private guard
 * state and there is no new multiple-definition surface.
 *
 * Sampling rate is SIMPLE_MEM_GUARD_RATE=N (unset/0 = disabled -- the
 * zero-overhead default: rt_mem_guard_should_sample degenerates to one
 * cached-int read plus an early return, and rt_mem_guard_is_slot degenerates
 * to one size_t compare, matching mem_guard.rs's documented off-path cost).
 */

#ifndef RUNTIME_MEMORY_GUARD_H
#define RUNTIME_MEMORY_GUARD_H

#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

#if !defined(_WIN32)
#define RT_MEM_GUARD_AVAILABLE 1
#include <sys/mman.h>
#else
/* No VirtualAlloc/VirtualProtect port yet -- sampling is a documented no-op
 * on Windows (rt_mem_guard_should_sample always returns 0), never a wrong
 * or crashing result. */
#define RT_MEM_GUARD_AVAILABLE 0
#endif

#define RT_MEM_GUARD_PAGE_SIZE ((size_t)4096)
#define RT_MEM_GUARD_FREE_RING_CAP 256
#define RT_MEM_GUARD_MAX_SLOTS 4096

typedef struct RtMemGuardSlot {
    uint8_t* user_ptr;   /* NULL = empty array slot, free for reuse */
    uint8_t* page_base;
    size_t total_pages;
    size_t size;         /* requested (unpadded) size, for realloc/reporting */
    int freed;
} RtMemGuardSlot;

static RtMemGuardSlot rt_mem_guard_slots[RT_MEM_GUARD_MAX_SLOTS];
static size_t rt_mem_guard_slot_hwm = 0; /* high-water mark of used indices */
static uintptr_t rt_mem_guard_free_ring[RT_MEM_GUARD_FREE_RING_CAP];
static size_t rt_mem_guard_free_ring_head = 0;
static size_t rt_mem_guard_free_ring_len = 0;
static uint64_t rt_mem_guard_sample_counter = 0;
static int64_t rt_mem_guard_sampled_total = 0;

static int rt_mem_guard_rate_cached = -1;
static long rt_mem_guard_rate_value = 0;

/* Cached SIMPLE_MEM_GUARD_RATE, read via getenv exactly once. 0 = disabled. */
static long rt_mem_guard_rate(void) {
    if (rt_mem_guard_rate_cached < 0) {
        const char* v = getenv("SIMPLE_MEM_GUARD_RATE");
        long parsed = 0;
        if (v != NULL && v[0] != '\0') {
            char* end = NULL;
            long n = strtol(v, &end, 10);
            if (end != v && n > 0) parsed = n;
        }
        rt_mem_guard_rate_value = parsed;
        rt_mem_guard_rate_cached = 1;
    }
    return rt_mem_guard_rate_value;
}

/* Deterministic 1-in-N sampling decision (never rand() -- CI/fixture
 * determinism, matching mem_guard.rs's mem_guard_should_sample). */
static int rt_mem_guard_should_sample(size_t size) {
    (void)size;
    long rate = rt_mem_guard_rate();
    if (rate <= 0) return 0;
    uint64_t n = rt_mem_guard_sample_counter++;
    return (n % (uint64_t)rate) == 0;
}

#if RT_MEM_GUARD_AVAILABLE

/* Allocate `size` bytes on their own guard-paged mmap slot. Right-aligns so
 * the allocation's last byte lands on the last byte of the last data page
 * (GWP-ASan default -- catches overflow). Returns NULL on mmap/mprotect
 * failure or a full slot table; caller must fall back to the normal
 * allocator in either case. */
static void* rt_mem_guard_alloc_sampled(size_t size) {
    if (size == 0) return NULL;

    size_t idx = RT_MEM_GUARD_MAX_SLOTS;
    for (size_t i = 0; i < RT_MEM_GUARD_MAX_SLOTS; i++) {
        if (rt_mem_guard_slots[i].user_ptr == NULL) { idx = i; break; }
    }
    if (idx == RT_MEM_GUARD_MAX_SLOTS) return NULL;

    size_t data_pages = (size + RT_MEM_GUARD_PAGE_SIZE - 1) / RT_MEM_GUARD_PAGE_SIZE;
    if (data_pages == 0) data_pages = 1;
    size_t total_pages = data_pages + 2; /* leading + trailing guard page */
    size_t map_len = total_pages * RT_MEM_GUARD_PAGE_SIZE;

    void* base = mmap(NULL, map_len, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (base == MAP_FAILED) return NULL;

    uint8_t* page_base = (uint8_t*)base;
    uint8_t* trailing_page = page_base + RT_MEM_GUARD_PAGE_SIZE * (1 + data_pages);

    if (mprotect(page_base, RT_MEM_GUARD_PAGE_SIZE, PROT_NONE) != 0 ||
        mprotect(trailing_page, RT_MEM_GUARD_PAGE_SIZE, PROT_NONE) != 0) {
        munmap(base, map_len);
        return NULL;
    }

    /* Right-align within the data region [page_base+PAGE, trailing_page). */
    uint8_t* user_ptr = trailing_page - size;

    rt_mem_guard_slots[idx].user_ptr = user_ptr;
    rt_mem_guard_slots[idx].page_base = page_base;
    rt_mem_guard_slots[idx].total_pages = total_pages;
    rt_mem_guard_slots[idx].size = size;
    rt_mem_guard_slots[idx].freed = 0;
    if (idx >= rt_mem_guard_slot_hwm) rt_mem_guard_slot_hwm = idx + 1;
    rt_mem_guard_sampled_total++;
    return user_ptr;
}

static RtMemGuardSlot* rt_mem_guard_find(void* ptr) {
    if (rt_mem_guard_slot_hwm == 0 || ptr == NULL) return NULL;
    for (size_t i = 0; i < rt_mem_guard_slot_hwm; i++) {
        if (rt_mem_guard_slots[i].user_ptr == (uint8_t*)ptr) return &rt_mem_guard_slots[i];
    }
    return NULL;
}

/* O(1) on the disabled path (rt_mem_guard_slot_hwm stays 0 forever when
 * SIMPLE_MEM_GUARD_RATE is unset, since nothing is ever sampled). */
static int rt_mem_guard_is_slot(void* ptr) {
    return rt_mem_guard_find(ptr) != NULL;
}

/* Free a sampled guard slot: PROT_NONEs the whole mapping (traps any further
 * read/write, including UAF) and enqueues it for delayed real munmap once
 * the ring evicts it. Returns 0 for an unknown pointer or a double free
 * (slot already marked freed) -- caller must refuse to treat those as a
 * normal free. */
static int rt_mem_guard_free_sampled(void* ptr) {
    RtMemGuardSlot* slot = rt_mem_guard_find(ptr);
    if (slot == NULL) return 0;
    if (slot->freed) return 0; /* double free of a guard slot -- refuse */
    slot->freed = 1;
    mprotect(slot->page_base, slot->total_pages * RT_MEM_GUARD_PAGE_SIZE, PROT_NONE);

    if (rt_mem_guard_free_ring_len == RT_MEM_GUARD_FREE_RING_CAP) {
        uintptr_t evict_ptr = rt_mem_guard_free_ring[rt_mem_guard_free_ring_head];
        rt_mem_guard_free_ring_head =
            (rt_mem_guard_free_ring_head + 1) % RT_MEM_GUARD_FREE_RING_CAP;
        rt_mem_guard_free_ring_len--;
        RtMemGuardSlot* evicted = rt_mem_guard_find((void*)evict_ptr);
        if (evicted != NULL) {
            munmap(evicted->page_base, evicted->total_pages * RT_MEM_GUARD_PAGE_SIZE);
            evicted->user_ptr = NULL; /* free the array slot for reuse */
        }
    }
    size_t tail = (rt_mem_guard_free_ring_head + rt_mem_guard_free_ring_len)
                  % RT_MEM_GUARD_FREE_RING_CAP;
    rt_mem_guard_free_ring[tail] = (uintptr_t)ptr;
    rt_mem_guard_free_ring_len++;
    return 1;
}

#else /* !RT_MEM_GUARD_AVAILABLE */

static void* rt_mem_guard_alloc_sampled(size_t size) { (void)size; return NULL; }
static int rt_mem_guard_is_slot(void* ptr) { (void)ptr; return 0; }
static int rt_mem_guard_free_sampled(void* ptr) { (void)ptr; return 0; }
/* Both realloc paths -- runtime_memory.c (hosted/JIT) and runtime_native.c
 * (native/AOT) -- call rt_mem_guard_find unconditionally; only the *result* is
 * runtime-gated (`if (rt_mem_guard_is_slot(ptr))` / `slot ? slot->size : 0`),
 * so the call still has to COMPILE here. Without this stub the C runtime does
 * not build at all on Windows: `implicit declaration of function
 * 'rt_mem_guard_find'` then `initialization of 'RtMemGuardSlot *' from 'int'`.
 * Returning NULL is the correct answer when no allocation is ever sampled. */
static RtMemGuardSlot* rt_mem_guard_find(void* ptr) { (void)ptr; return NULL; }

#endif /* RT_MEM_GUARD_AVAILABLE */

/* Total number of rt_alloc calls ever routed onto a guard slot in this
 * process (native mirror of the interpreter's rt_mem_guard_stats extern).
 * 0 whenever SIMPLE_MEM_GUARD_RATE is unset. */
static int64_t rt_mem_guard_stats_native(void) {
    return rt_mem_guard_sampled_total;
}

#endif /* RUNTIME_MEMORY_GUARD_H */
