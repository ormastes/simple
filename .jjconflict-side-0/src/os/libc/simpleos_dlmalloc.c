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

/* ====================================================================
 * Free-list node — stored in the payload area of free blocks
 * ==================================================================== */

typedef struct free_node {
    struct free_node *next;
    struct free_node *prev;
} free_node;

static free_node free_list_sentinel = { &free_list_sentinel, &free_list_sentinel };

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

/* ====================================================================
 * Internal helpers
 * ==================================================================== */

static void *_mmap_pages(size_t size) {
    size = (size + HEAP_PAGE_SIZE - 1) & ~(size_t)(HEAP_PAGE_SIZE - 1);
    int64_t addr = simpleos_syscall(10, 0, (int64_t)size,
                                     3 /* PROT_READ|PROT_WRITE */, 0, 0);
    if (addr <= 0) return NULL;
    return (void *)addr;
}

/* Check whether ptr falls within any known heap region */
static int _in_heap(const char *ptr) {
    for (int i = 0; i < region_count; i++) {
        if (ptr >= regions[i].base &&
            ptr <  regions[i].base + regions[i].size)
            return 1;
    }
    return 0;
}

static void _free_list_insert(free_node *node) {
    node->next = free_list_sentinel.next;
    node->prev = &free_list_sentinel;
    free_list_sentinel.next->prev = node;
    free_list_sentinel.next = node;
}

static void _free_list_remove(free_node *node) {
    node->prev->next = node->next;
    node->next->prev = node->prev;
}

/* ====================================================================
 * Public API
 * ==================================================================== */

void *malloc(size_t size) {
    if (size == 0) return NULL;

    /* Round up: header + payload, aligned to 16 bytes, at least MIN_ALLOC */
    size = (size + HEADER_SIZE + 15) & ~(size_t)15;
    if (size < MIN_ALLOC) size = MIN_ALLOC;

    /* Search free list for best fit */
    free_node *best = NULL;
    size_t best_size = (size_t)-1;
    for (free_node *n = free_list_sentinel.next;
         n != &free_list_sentinel; n = n->next) {
        block_header *hdr = (block_header *)((char *)n - HEADER_SIZE);
        size_t bsize = BLOCK_SIZE(hdr);
        if (bsize >= size && bsize < best_size) {
            best = n;
            best_size = bsize;
            if (bsize == size) break; /* exact fit */
        }
    }

    if (best) {
        block_header *hdr = (block_header *)((char *)best - HEADER_SIZE);
        _free_list_remove(best);
        size_t bsize = BLOCK_SIZE(hdr);

        /* Split if the remainder is large enough for a standalone block */
        if (bsize - size >= MIN_ALLOC) {
            block_header *split = (block_header *)((char *)hdr + size);
            split->size = bsize - size;
            split->prev_size = size;
            BLOCK_SET_FREE(split);
            hdr->size = size;
            _free_list_insert((free_node *)((char *)split + HEADER_SIZE));

            /* Update following block's prev_size */
            block_header *next = NEXT_BLOCK(split);
            if (_in_heap((char *)next))
                next->prev_size = BLOCK_SIZE(split);
        }

        BLOCK_SET_INUSE(hdr);
        return (char *)hdr + HEADER_SIZE;
    }

    /* No suitable free block — allocate new pages */
    size_t alloc_size = size;
    if (alloc_size < 64 * 1024) alloc_size = 64 * 1024; /* min 64 KB chunk */

    void *pages = _mmap_pages(alloc_size);
    if (!pages) return NULL;

    /* Register the new region */
    if (region_count < MAX_REGIONS) {
        regions[region_count].base = (char *)pages;
        regions[region_count].size = alloc_size;
        region_count++;
    }

    block_header *hdr = (block_header *)pages;
    hdr->size = alloc_size;
    hdr->prev_size = 0;

    /* Split off the requested portion, put remainder on free list */
    if (alloc_size - size >= MIN_ALLOC) {
        hdr->size = size;
        BLOCK_SET_INUSE(hdr);
        block_header *remainder = (block_header *)((char *)hdr + size);
        remainder->size = alloc_size - size;
        remainder->prev_size = size;
        BLOCK_SET_FREE(remainder);
        _free_list_insert((free_node *)((char *)remainder + HEADER_SIZE));
        return (char *)hdr + HEADER_SIZE;
    }

    BLOCK_SET_INUSE(hdr);
    return (char *)hdr + HEADER_SIZE;
}

void free(void *ptr) {
    if (!ptr) return;

    block_header *hdr = (block_header *)((char *)ptr - HEADER_SIZE);
    BLOCK_SET_FREE(hdr);

    /* Coalesce with the next contiguous block if it is free */
    block_header *next = NEXT_BLOCK(hdr);
    if (_in_heap((char *)next) && !BLOCK_INUSE(next)) {
        _free_list_remove((free_node *)((char *)next + HEADER_SIZE));
        hdr->size = BLOCK_SIZE(hdr) + BLOCK_SIZE(next);
    }

    /* Coalesce with the previous contiguous block if it is free */
    if (hdr->prev_size > 0) {
        block_header *prev = (block_header *)((char *)hdr - hdr->prev_size);
        if (_in_heap((char *)prev) && !BLOCK_INUSE(prev)) {
            _free_list_remove((free_node *)((char *)prev + HEADER_SIZE));
            prev->size = BLOCK_SIZE(prev) + BLOCK_SIZE(hdr);
            hdr = prev; /* coalesced block starts at prev */
        }
    }

    /* Update the following block's prev_size */
    next = NEXT_BLOCK(hdr);
    if (_in_heap((char *)next))
        next->prev_size = BLOCK_SIZE(hdr);

    _free_list_insert((free_node *)((char *)hdr + HEADER_SIZE));
}

void *calloc(size_t nmemb, size_t size) {
    size_t total = nmemb * size;
    /* Overflow check */
    if (nmemb && total / nmemb != size) return NULL;
    void *p = malloc(total);
    if (p) memset(p, 0, total);
    return p;
}

void *realloc(void *ptr, size_t size) {
    if (!ptr) return malloc(size);
    if (size == 0) { free(ptr); return NULL; }

    block_header *hdr = (block_header *)((char *)ptr - HEADER_SIZE);
    size_t old_payload = BLOCK_SIZE(hdr) - HEADER_SIZE;

    /* Shrink or same size: keep the current block */
    if (size <= old_payload) return ptr;

    /* Grow: allocate new, copy old data, free old */
    void *new_ptr = malloc(size);
    if (!new_ptr) return NULL;
    memcpy(new_ptr, ptr, old_payload);
    free(ptr);
    return new_ptr;
}
