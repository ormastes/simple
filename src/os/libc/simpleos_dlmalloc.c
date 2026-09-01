/*
 * SimpleOS dlmalloc — free-list allocator with coalescing
 *
 * Replaces the bump allocator in simpleos_libc.c. The bump allocator never
 * frees memory, so compilers that allocate/free gigabytes will OOM.
 *
 * Design:
 *   - Each block has a header: [size_with_flags | prev_size]
 *   - Bit 0 of size: 1 = in-use, 0 = free
 *   - Free blocks are linked in a doubly-linked circular free list
 *   - Allocation: best-fit scan of the free list
 *   - Free: coalesce with adjacent free blocks (both forward and backward)
 *   - New pages obtained via Mmap syscall (10)
 */

#include "include/stdlib.h"
#include "include/string.h"
#include <stdint.h>

extern int64_t simpleos_syscall(int64_t, int64_t, int64_t, int64_t,
                                 int64_t, int64_t);

#define HEAP_PAGE_SIZE 4096
#define MIN_ALLOC      32       /* minimum block size (header + payload) */
#define HEADER_SIZE    16       /* sizeof(block_header) = 2 * 8 bytes   */

/* ====================================================================
 * Block header
 *
 * size:      block size including header, bit 0 = in-use flag
 * prev_size: size of the physically previous block (for backward coalescing)
 * ==================================================================== */

typedef struct block_header {
    size_t size;        /* Size including header; bit 0 = in-use */
    size_t prev_size;   /* Size of previous contiguous block     */
} block_header;

#define BLOCK_SIZE(b)       ((b)->size & ~(size_t)3)
#define BLOCK_INUSE(b)      ((b)->size & 1)
#define BLOCK_SET_INUSE(b)  ((b)->size |= 1)
#define BLOCK_SET_FREE(b)   ((b)->size &= ~(size_t)1)
#define NEXT_BLOCK(b)       ((block_header *)((char *)(b) + BLOCK_SIZE(b)))
#define BLOCK_FLAGS_VALID(b) (((b)->size & (size_t)2) == 0)

/* ====================================================================
 * Free-list node — stored in the payload area of free blocks
 * ==================================================================== */

typedef struct free_node {
    struct free_node *next;
    struct free_node *prev;
} free_node;

static free_node free_list_sentinel = { &free_list_sentinel, &free_list_sentinel };
static volatile int allocator_lock = 0;

/*
 * Track allocated regions so we can determine whether a next-block pointer
 * is still within a valid heap region.  We track each mmap'd region.
 */
#define MAX_REGIONS 256

typedef struct {
    char  *base;
    size_t size;
} heap_region;

static heap_region regions[MAX_REGIONS];
static int region_count = 0;
/* A failed internal list transaction must never be followed by a best-effort
 * allocation from potentially incomplete metadata. */
static int allocator_poisoned = 0;

#if defined(SIMPLEOS_DLMALLOC_TESTING)
static int allocator_test_fail_inserts = 0;
void simpleos_dlmalloc_test_fail_next_insert(void) {
    allocator_test_fail_inserts = 1;
}
#endif

/* ====================================================================
 * Internal helpers
 * ==================================================================== */

/* Overflow-checked size arithmetic.
 *
 * _checked_add and _checked_round_up were CALLED by _malloc_locked (and
 * _mmap_pages was called with an out-parameter it did not have) but were never
 * DEFINED anywhere in the tree — a half-landed hardening change. clang rejects
 * the file:
 *
 *   error: call to undeclared function '_checked_add'
 *   error: call to undeclared function '_checked_round_up'
 *   error: too many arguments to function call, expected single argument
 *          'size', have 2 arguments      (_mmap_pages)
 *
 * so simpleos_dlmalloc.c HAS NEVER COMPILED, and with it the whole SimpleOS
 * libc and every SimpleOS user payload on every architecture. Same defect class
 * as the runtime_native.c incident in .claude/rules/vcs.md: source that passes
 * every tree-structure guard and is nonsense to a compiler.
 *
 * The contract is recoverable unambiguously from the call sites, so these are
 * completed rather than the calls reverted:
 *   * `!_checked_add(size, HEADER_SIZE, &requested)` must mean "false on
 *     overflow", since the caller returns NULL (allocation failure) on false.
 *   * `_checked_round_up(requested, 16, &size)` rounds up to an alignment that
 *     is a power of two, likewise false on overflow.
 * Returning false rather than saturating is what makes them a hardening
 * measure: a saturated size would be handed to mmap and could wrap a later
 * pointer computation.
 */
static int _checked_add(size_t a, size_t b, size_t *out) {
    if (b > (size_t)-1 - a) return 0;
    *out = a + b;
    return 1;
}

static int _checked_round_up(size_t value, size_t align, size_t *out) {
    /* align is always a compile-time power of two at the call sites; assert the
     * precondition rather than silently computing nonsense if that changes. */
    if (align == 0 || (align & (align - 1)) != 0) return 0;
    if (value > (size_t)-1 - (align - 1)) return 0;
    *out = (value + align - 1) & ~(align - 1);
    return 1;
}

/* Map at least `size` bytes and report through *mapped_out how many bytes were
 * ACTUALLY mapped after page rounding.
 *
 * The out-parameter is the whole point of the caller's change and is not
 * cosmetic: the caller stores the result as both the heap region's size and the
 * initial block header's size, and then splits the remainder onto the free
 * list. Using the caller's un-rounded request there would under-report the
 * region by up to a page, so the tail of every mapping would be invisible to
 * the allocator — leaked at best, and outside _region_for_address's ownership
 * check (which free/realloc use as their authority) at worst. */
static void *_mmap_pages(size_t size, size_t *mapped_out) {
    size_t mapped;
    if (!_checked_round_up(size, HEAP_PAGE_SIZE, &mapped)) return NULL;
    int64_t addr = simpleos_syscall(10, 0, (int64_t)mapped,
                                     3 /* PROT_READ|PROT_WRITE */, 0, 0);
    if (addr <= 0) return NULL;
    if (mapped_out) *mapped_out = mapped;
    return (void *)addr;
}

static heap_region *_region_for_address(uintptr_t address) {
    for (int i = 0; i < region_count; i++) {
        uintptr_t base = (uintptr_t)regions[i].base;
        if (address >= base && address - base < regions[i].size)
            return &regions[i];
    }
    return NULL;
}

/* Validate a candidate header by walking only the registered region's
 * well-formed physical block chain. This rejects interior, forged and stale
 * pointers before any free-list pointer is read or written. */
static int _validated_block(block_header *candidate, heap_region **out_region) {
    heap_region *region = _region_for_address((uintptr_t)candidate);
    if (!region) return 0;
    uintptr_t base = (uintptr_t)region->base;
    uintptr_t target = (uintptr_t)candidate;
    if (target < base || ((target - base) & 15U) != 0) return 0;
    size_t offset = 0;
    size_t expected_prev_size = 0;
    while (offset < region->size) {
        if (region->size - offset < HEADER_SIZE) return 0;
        block_header *current = (block_header *)(base + offset);
        size_t size = BLOCK_SIZE(current);
        if (!BLOCK_FLAGS_VALID(current) || current->prev_size != expected_prev_size || size < MIN_ALLOC ||
            (size & 15U) != 0 || size > region->size - offset) return 0;
        if ((uintptr_t)current == target) {
            *out_region = region;
            return 1;
        }
        expected_prev_size = size;
        offset += size;
    }
    return 0;
}

/* Validate the complete physical chain before a free operation changes a
 * boundary backlink. `_validated_block` intentionally stops at its target;
 * free additionally needs to know that every successor it may retarget is
 * well formed before it unlinks or coalesces anything. */
static int _validated_region_chain(heap_region *region) {
    uintptr_t base = (uintptr_t)region->base;
    size_t offset = 0;
    size_t expected_prev_size = 0;
    while (offset < region->size) {
        if (region->size - offset < HEADER_SIZE) return 0;
        block_header *current = (block_header *)(base + offset);
        size_t size = BLOCK_SIZE(current);
        if (!BLOCK_FLAGS_VALID(current) || current->prev_size != expected_prev_size ||
            size < MIN_ALLOC || (size & 15U) != 0 || size > region->size - offset) return 0;
        expected_prev_size = size;
        offset += size;
    }
    return offset == region->size;
}

static block_header *_next_in_region(block_header *hdr, heap_region *region) {
    uintptr_t current = (uintptr_t)hdr;
    uintptr_t base = (uintptr_t)region->base;
    size_t offset = (size_t)(current - base);
    size_t size = BLOCK_SIZE(hdr);
    if (size > region->size - offset || size == region->size - offset) return NULL;
    return (block_header *)(current + size);
}

/* This libc allocator has shared global region/free-list state. A compact
 * spin lock is the only portable primitive available in every shipped
 * SimpleOS sysroot; allocation operations never call the public wrappers
 * while holding it, so recursion is avoided. */
static void _allocator_lock(void) {
    while (__sync_lock_test_and_set(&allocator_lock, 1)) { }
}

static void _allocator_unlock(void) {
    __sync_lock_release(&allocator_lock);
}

static int _known_free_node(free_node *candidate) {
    if (candidate == &free_list_sentinel) return 1;
    for (int i = 0; i < region_count; ++i) {
        uintptr_t base = (uintptr_t)regions[i].base;
        size_t offset = 0;
        size_t expected_prev_size = 0;
        while (offset < regions[i].size) {
            if (regions[i].size - offset < HEADER_SIZE) return 0;
            block_header *hdr = (block_header *)(base + offset);
            size_t size = BLOCK_SIZE(hdr);
            if (!BLOCK_FLAGS_VALID(hdr) || hdr->prev_size != expected_prev_size || size < MIN_ALLOC ||
                (size & 15U) != 0 || size > regions[i].size - offset) return 0;
            if (!BLOCK_INUSE(hdr) && candidate == (free_node *)((char *)hdr + HEADER_SIZE)) return 1;
            expected_prev_size = size;
            offset += size;
        }
    }
    return 0;
}

static int _free_node_links_valid(free_node *node) {
    if (!_known_free_node(node)) return 0;
    free_node *next = node->next;
    free_node *prev = node->prev;
    if (!_known_free_node(next) || !_known_free_node(prev)) return 0;
    return next->prev == node && prev->next == node;
}

/* Count physical free blocks before following mutable list links.  During
 * allocation the list must contain exactly this many nodes, which bounds a
 * corrupted self-consistent cycle and fails closed instead of spinning while
 * the allocator lock is held. */
static int _physical_free_node_count(size_t *out) {
    size_t count = 0;
    for (int i = 0; i < region_count; ++i) {
        uintptr_t base = (uintptr_t)regions[i].base;
        size_t offset = 0;
        size_t expected_prev_size = 0;
        while (offset < regions[i].size) {
            if (regions[i].size - offset < HEADER_SIZE) return 0;
            block_header *hdr = (block_header *)(base + offset);
            size_t size = BLOCK_SIZE(hdr);
            if (!BLOCK_FLAGS_VALID(hdr) || hdr->prev_size != expected_prev_size || size < MIN_ALLOC ||
                (size & 15U) != 0 || size > regions[i].size - offset) return 0;
            if (!BLOCK_INUSE(hdr)) {
                if (count == (size_t)-1) return 0;
                count++;
            }
            expected_prev_size = size;
            offset += size;
        }
    }
    *out = count;
    return 1;
}

static int _free_list_insert(free_node *node) {
#if defined(SIMPLEOS_DLMALLOC_TESTING)
    if (allocator_test_fail_inserts > 0) {
        allocator_test_fail_inserts--;
        return 0;
    }
#endif
    if (!_known_free_node(&free_list_sentinel) ||
        !_free_node_links_valid(free_list_sentinel.next)) return 0;
    node->next = free_list_sentinel.next;
    node->prev = &free_list_sentinel;
    free_list_sentinel.next->prev = node;
    free_list_sentinel.next = node;
    return 1;
}

static int _free_list_remove(free_node *node) {
    if (!_free_node_links_valid(node)) return 0;
    node->prev->next = node->next;
    node->next->prev = node->prev;
    return 1;
}

/* ====================================================================
 * Public API
 * ==================================================================== */

static void *_malloc_locked(size_t size) {
    if (size == 0 || allocator_poisoned) return NULL;

    /* Round up: header + payload, aligned to 16 bytes, at least MIN_ALLOC */
    size_t requested;
    if (!_checked_add(size, HEADER_SIZE, &requested) ||
        !_checked_round_up(requested, 16, &size)) return NULL;
    if (size < MIN_ALLOC) size = MIN_ALLOC;

    /* Search free list for best fit */
    free_node *best = NULL;
    size_t best_size = (size_t)-1;
    size_t free_nodes_remaining = 0;
    if (!_physical_free_node_count(&free_nodes_remaining)) return NULL;
    for (free_node *n = free_list_sentinel.next;
         n != &free_list_sentinel;) {
        if (free_nodes_remaining == 0) return NULL;
        free_nodes_remaining--;
        if (!_free_node_links_valid(n)) return NULL;
        block_header *hdr = (block_header *)((char *)n - HEADER_SIZE);
        size_t bsize = BLOCK_SIZE(hdr);
        if (bsize >= size && bsize < best_size) {
            best = n;
            best_size = bsize;
        }
        n = n->next;
    }
    if (free_nodes_remaining != 0) return NULL;

    if (best) {
        block_header *hdr = (block_header *)((char *)best - HEADER_SIZE);
        heap_region *region = NULL;
        if (!_validated_block(hdr, &region)) return NULL;
        if (!_free_list_remove(best)) return NULL;
        size_t bsize = BLOCK_SIZE(hdr);

        /* Split if the remainder is large enough for a standalone block */
        if (bsize - size >= MIN_ALLOC) {
            block_header *split = (block_header *)((char *)hdr + size);
            split->size = bsize - size;
            split->prev_size = size;
            BLOCK_SET_FREE(split);
            hdr->size = size;

            /* Update following block's prev_size */
            block_header *next = _next_in_region(split, region);
            if (next)
                next->prev_size = BLOCK_SIZE(split);
            if (!_free_list_insert((free_node *)((char *)split + HEADER_SIZE))) {
                /* Restore the exact former free block before returning. */
                if (next) next->prev_size = bsize;
                hdr->size = bsize;
                if (!_free_list_insert(best)) allocator_poisoned = 1;
                return NULL;
            }
        }

        BLOCK_SET_INUSE(hdr);
        return (char *)hdr + HEADER_SIZE;
    }

    /* No suitable free block — allocate new pages */
    size_t alloc_size = size;
    if (alloc_size < 64 * 1024) alloc_size = 64 * 1024; /* min 64 KB chunk */

    /* Region metadata is the ownership authority for free/realloc. Refuse
     * before mmap so exhaustion cannot leak or hand out an untracked region. */
    if (region_count >= MAX_REGIONS) return NULL;
    size_t mapped_size = 0;
    void *pages = _mmap_pages(alloc_size, &mapped_size);
    if (!pages) return NULL;

    /* Register the new region */
    regions[region_count].base = (char *)pages;
    regions[region_count].size = mapped_size;
    region_count++;

    block_header *hdr = (block_header *)pages;
    hdr->size = mapped_size;
    hdr->prev_size = 0;

    /* Split off the requested portion, put remainder on free list */
    if (mapped_size - size >= MIN_ALLOC) {
        hdr->size = size;
        BLOCK_SET_INUSE(hdr);
        block_header *remainder = (block_header *)((char *)hdr + size);
        remainder->size = mapped_size - size;
        remainder->prev_size = size;
        BLOCK_SET_FREE(remainder);
        if (!_free_list_insert((free_node *)((char *)remainder + HEADER_SIZE))) {
            /* Do not retain an unreturnable live block in region metadata.
             * A failed list operation means an internal invariant failed, so
             * unregister this mapping and stop future allocations fail closed. */
            region_count--;
            allocator_poisoned = 1;
            return NULL;
        }
        return (char *)hdr + HEADER_SIZE;
    }

    BLOCK_SET_INUSE(hdr);
    return (char *)hdr + HEADER_SIZE;
}

static void _free_locked(void *ptr) {
    if (!ptr || allocator_poisoned) return;

    uintptr_t raw_ptr = (uintptr_t)ptr;
    if (raw_ptr < HEADER_SIZE) return;
    block_header *hdr = (block_header *)(raw_ptr - HEADER_SIZE);
    heap_region *region = NULL;
    if (!_validated_block(hdr, &region) || !_validated_region_chain(region) ||
        !BLOCK_INUSE(hdr)) return;

    /* Validate every unlink before mutating physical headers. This keeps a
     * failed two-sided coalesce transactional: the original live block stays
     * live rather than becoming an unlinked free leak. */
    block_header *next = _next_in_region(hdr, region);
    if (next && _validated_block(next, &region) && !BLOCK_INUSE(next)) {
        if (!_free_node_links_valid((free_node *)((char *)next + HEADER_SIZE))) return;
    }

    block_header *prev = NULL;
    if (hdr->prev_size > 0) {
        size_t offset = (size_t)((uintptr_t)hdr - (uintptr_t)region->base);
        if (hdr->prev_size <= offset) {
            prev = (block_header *)((char *)hdr - hdr->prev_size);
            if (_validated_block(prev, &region) && _next_in_region(prev, region) == hdr &&
                !BLOCK_INUSE(prev)) {
                if (!_free_node_links_valid((free_node *)((char *)prev + HEADER_SIZE))) return;
            } else {
                prev = NULL;
            }
        }
    }

    block_header *original_hdr = hdr;
    size_t original_hdr_size = hdr->size;
    block_header *forward_next = next;
    int merged_forward = next && !BLOCK_INUSE(next);
    size_t original_next_size = forward_next ? forward_next->size : 0;
    size_t original_prev_size = prev ? prev->size : 0;
    BLOCK_SET_FREE(hdr);
    if (merged_forward) {
        if (!_free_list_remove((free_node *)((char *)forward_next + HEADER_SIZE))) {
            BLOCK_SET_INUSE(hdr);
            return;
        }
        hdr->size = BLOCK_SIZE(hdr) + BLOCK_SIZE(forward_next);
    }
    if (prev) {
        if (!_free_list_remove((free_node *)((char *)prev + HEADER_SIZE))) {
            /* Undo the already-completed forward merge exactly.  Returning
             * with the successor backlink from the larger hdr would make the
             * next allocation observe a malformed physical chain. */
            if (merged_forward) {
                hdr->size = original_hdr_size;
                forward_next->size = original_next_size;
                if (!_free_list_insert((free_node *)((char *)forward_next + HEADER_SIZE)))
                    allocator_poisoned = 1;
            } else {
                hdr->size = original_hdr_size;
            }
            /* The caller's block was live when the transaction began.  It
             * must remain live if the backward unlink cannot be completed;
             * otherwise it is a physical free block absent from the list. */
            BLOCK_SET_INUSE(hdr);
            return;
        }
        prev->size = BLOCK_SIZE(prev) + BLOCK_SIZE(hdr);
        hdr = prev;
    }

    /* Update the following block's prev_size */
    next = _next_in_region(hdr, region);
    size_t original_after_prev_size = next ? next->prev_size : 0;
    if (next)
        next->prev_size = BLOCK_SIZE(hdr);

    if (!_free_list_insert((free_node *)((char *)hdr + HEADER_SIZE))) {
        /* The final publication failed after one or both adjacent free
         * blocks may have been unlinked. Restore the exact pre-free graph
         * before poisoning; a poisoned allocator may refuse future work, but
         * it must never retain a malformed physical/list state for callers
         * that still release existing allocations. */
        if (next) next->prev_size = original_after_prev_size;
        if (prev) prev->size = original_prev_size;
        original_hdr->size = original_hdr_size;
        BLOCK_SET_INUSE(original_hdr);
        if (merged_forward) forward_next->size = original_next_size;
        if (prev && !_free_list_insert((free_node *)((char *)prev + HEADER_SIZE)))
            allocator_poisoned = 1;
        if (merged_forward && !_free_list_insert((free_node *)((char *)forward_next + HEADER_SIZE)))
            allocator_poisoned = 1;
        allocator_poisoned = 1;
    }
}

static void *_calloc_locked(size_t nmemb, size_t size) {
    if (nmemb != 0 && size > (size_t)-1 / nmemb) return NULL;
    size_t total = nmemb * size;
    void *p = _malloc_locked(total);
    if (p) memset(p, 0, total);
    return p;
}

static void *_realloc_locked(void *ptr, size_t size) {
    if (!ptr) return _malloc_locked(size);
    if (size == 0) { _free_locked(ptr); return NULL; }

    uintptr_t raw_ptr = (uintptr_t)ptr;
    if (raw_ptr < HEADER_SIZE) return NULL;
    block_header *hdr = (block_header *)(raw_ptr - HEADER_SIZE);
    heap_region *region = NULL;
    if (!_validated_block(hdr, &region) || !BLOCK_INUSE(hdr)) return NULL;
    size_t old_payload = BLOCK_SIZE(hdr) - HEADER_SIZE;

    /* Shrink or same size: keep the current block */
    if (size <= old_payload) return ptr;

    /* Grow: allocate new, copy old data, free old */
    void *new_ptr = _malloc_locked(size);
    if (!new_ptr) return NULL;
    memcpy(new_ptr, ptr, old_payload);
    _free_locked(ptr);
    return new_ptr;
}

void *malloc(size_t size) {
    void *result;
    _allocator_lock();
    result = _malloc_locked(size);
    _allocator_unlock();
    return result;
}

void free(void *ptr) {
    _allocator_lock();
    _free_locked(ptr);
    _allocator_unlock();
}

void *calloc(size_t nmemb, size_t size) {
    void *result;
    _allocator_lock();
    result = _calloc_locked(nmemb, size);
    _allocator_unlock();
    return result;
}

void *realloc(void *ptr, size_t size) {
    void *result;
    _allocator_lock();
    result = _realloc_locked(ptr, size);
    _allocator_unlock();
    return result;
}
