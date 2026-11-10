#ifndef SIMPLEOS_RECLAIM_HEAP_H
#define SIMPLEOS_RECLAIM_HEAP_H

#include <stddef.h>
#include <stdint.h>

/* Single-owner freestanding heap. Explicit free is the ONLY release boundary:
 * retained RuntimeValue objects are never reclaimed by frame-wide rewinding.
 * Physical links coalesce neighbours; size bins avoid scanning live objects.
 * The caller supplies 16-byte-aligned storage and serializes access, as it did
 * for the former bump heap. No allocation moves except explicit realloc. */
typedef struct SimpleosHeapBlock SimpleosHeapBlock;
struct SimpleosHeapBlock {
    size_t span_flags;
    SimpleosHeapBlock *previous;
    SimpleosHeapBlock *free_next;
    SimpleosHeapBlock *free_previous;
};

#define SIMPLEOS_HEAP_BINS 32
#define SIMPLEOS_HEAP_ALIGNMENT 16u
#define SIMPLEOS_HEAP_LIVE ((size_t)1)

typedef struct {
    unsigned char *storage;
    size_t capacity;
    size_t used;
    SimpleosHeapBlock *last;
    SimpleosHeapBlock *bins[SIMPLEOS_HEAP_BINS];
} SimpleosReclaimHeap;

_Static_assert(sizeof(SimpleosHeapBlock) % SIMPLEOS_HEAP_ALIGNMENT == 0,
               "heap header must preserve payload alignment");

static inline size_t simpleos_reclaim_span(const SimpleosHeapBlock *block)
{
    return block->span_flags & ~(size_t)15;
}

static inline unsigned simpleos_reclaim_bin(size_t span)
{
    unsigned bin = 0;
    for (span >>= 5; span > 1 && bin + 1 < SIMPLEOS_HEAP_BINS; span >>= 1)
        ++bin;
    return bin;
}

static inline SimpleosHeapBlock *simpleos_reclaim_next(
    SimpleosReclaimHeap *heap, SimpleosHeapBlock *block)
{
    unsigned char *next = (unsigned char *)block + simpleos_reclaim_span(block);
    return next < heap->storage + heap->used ? (SimpleosHeapBlock *)next : NULL;
}

static inline void simpleos_reclaim_unlink(SimpleosReclaimHeap *heap,
                                         SimpleosHeapBlock *block)
{
    unsigned bin = simpleos_reclaim_bin(simpleos_reclaim_span(block));
    if (block->free_previous) block->free_previous->free_next = block->free_next;
    else heap->bins[bin] = block->free_next;
    if (block->free_next) block->free_next->free_previous = block->free_previous;
    block->free_previous = block->free_next = NULL;
}

static inline void simpleos_reclaim_insert(SimpleosReclaimHeap *heap,
                                         SimpleosHeapBlock *block)
{
    unsigned bin = simpleos_reclaim_bin(simpleos_reclaim_span(block));
    block->free_previous = NULL;
    block->free_next = heap->bins[bin];
    if (block->free_next) block->free_next->free_previous = block;
    heap->bins[bin] = block;
}

static inline int simpleos_reclaim_needed(size_t bytes, size_t *span)
{
    if (bytes == 0) bytes = 1;
    if (bytes > SIZE_MAX - sizeof(SimpleosHeapBlock) - 15) return 0;
    *span = sizeof(SimpleosHeapBlock) + ((bytes + 15) & ~(size_t)15);
    return 1;
}

static inline void *simpleos_reclaim_alloc(SimpleosReclaimHeap *heap, size_t bytes)
{
    size_t needed;
    if (!simpleos_reclaim_needed(bytes, &needed)) return NULL;
    SimpleosHeapBlock *block = NULL;
    for (unsigned bin = simpleos_reclaim_bin(needed); bin < SIMPLEOS_HEAP_BINS; ++bin) {
        for (block = heap->bins[bin]; block; block = block->free_next)
            if (simpleos_reclaim_span(block) >= needed) break;
        if (block) break;
    }
    if (block) {
        size_t available = simpleos_reclaim_span(block);
        simpleos_reclaim_unlink(heap, block);
        if (available - needed >= sizeof(SimpleosHeapBlock) + 16) {
            SimpleosHeapBlock *tail = (SimpleosHeapBlock *)((unsigned char *)block + needed);
            tail->span_flags = available - needed;
            tail->previous = block;
            block->span_flags = needed;
            SimpleosHeapBlock *after = simpleos_reclaim_next(heap, tail);
            if (after) after->previous = tail;
            else heap->last = tail;
            simpleos_reclaim_insert(heap, tail);
        }
        block->span_flags |= SIMPLEOS_HEAP_LIVE;
        return block + 1;
    }
    if (heap->used > heap->capacity || needed > heap->capacity - heap->used) return NULL;
    block = (SimpleosHeapBlock *)(heap->storage + heap->used);
    block->span_flags = needed | SIMPLEOS_HEAP_LIVE;
    block->previous = heap->last;
    block->free_next = block->free_previous = NULL;
    heap->last = block;
    heap->used += needed;
    return block + 1;
}

static inline void simpleos_reclaim_free(SimpleosReclaimHeap *heap, void *pointer)
{
    if (!pointer) return;
    SimpleosHeapBlock *block = (SimpleosHeapBlock *)pointer - 1;
    block->span_flags &= ~SIMPLEOS_HEAP_LIVE;
    SimpleosHeapBlock *next = simpleos_reclaim_next(heap, block);
    if (next && !(next->span_flags & SIMPLEOS_HEAP_LIVE)) {
        simpleos_reclaim_unlink(heap, next);
        block->span_flags += simpleos_reclaim_span(next);
    }
    SimpleosHeapBlock *previous = block->previous;
    if (previous && !(previous->span_flags & SIMPLEOS_HEAP_LIVE)) {
        simpleos_reclaim_unlink(heap, previous);
        previous->span_flags += simpleos_reclaim_span(block);
        block = previous;
    }
    next = simpleos_reclaim_next(heap, block);
    if (next) {
        next->previous = block;
        simpleos_reclaim_insert(heap, block);
    } else {
        heap->used = (size_t)((unsigned char *)block - heap->storage);
        heap->last = block->previous;
    }
}

static inline void *simpleos_reclaim_realloc(SimpleosReclaimHeap *heap,
                                            void *pointer, size_t bytes)
{
    if (!pointer) return simpleos_reclaim_alloc(heap, bytes);
    if (bytes == 0) { simpleos_reclaim_free(heap, pointer); return NULL; }
    size_t needed;
    if (!simpleos_reclaim_needed(bytes, &needed)) return NULL;
    SimpleosHeapBlock *block = (SimpleosHeapBlock *)pointer - 1;
    size_t old_span = simpleos_reclaim_span(block);
    if (needed <= old_span) {
        if (old_span - needed >= sizeof(SimpleosHeapBlock) + 16) {
            SimpleosHeapBlock *tail = (SimpleosHeapBlock *)((unsigned char *)block + needed);
            tail->span_flags = (old_span - needed) | SIMPLEOS_HEAP_LIVE;
            tail->previous = block;
            block->span_flags = needed | SIMPLEOS_HEAP_LIVE;
            SimpleosHeapBlock *after = simpleos_reclaim_next(heap, tail);
            if (after) after->previous = tail;
            else heap->last = tail;
            simpleos_reclaim_free(heap, tail + 1);
        }
        return pointer;
    }
    /* Preserve the common append path without allocating another live buffer. */
    if (heap->last == block && needed - old_span <= heap->capacity - heap->used) {
        heap->used += needed - old_span;
        block->span_flags = needed | SIMPLEOS_HEAP_LIVE;
        return pointer;
    }
    void *replacement = simpleos_reclaim_alloc(heap, bytes);
    if (!replacement) return NULL; /* Failed realloc retains the original owner. */
    size_t copy = old_span - sizeof(SimpleosHeapBlock);
    if (copy > bytes) copy = bytes;
    for (size_t i = 0; i < copy; ++i)
        ((unsigned char *)replacement)[i] = ((unsigned char *)pointer)[i];
    simpleos_reclaim_free(heap, pointer);
    return replacement;
}

#endif
