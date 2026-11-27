#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "../../../examples/09_embedded/simple_os/arch/common/simpleos_reclaim_heap.h"

static _Alignas(16) unsigned char storage[512 * 1024];
static SimpleosReclaimHeap heap;
static unsigned checks;
#define CHECK(condition) do { ++checks; if (!(condition)) { \
    fprintf(stderr, "FAIL line %d: %s\n", __LINE__, #condition); return 1; \
} } while (0)

static void runtime_freestanding_setup(void)
{
    memset(&heap, 0, sizeof(heap));
    heap.storage = storage;
    heap.capacity = sizeof(storage);
}

static int runtime_freestanding_check_alignment(void)
{
    runtime_freestanding_setup();
    void *pointers[50];
    for (size_t i = 0; i < 50; ++i) {
        pointers[i] = simpleos_reclaim_alloc(&heap, i);
        CHECK(pointers[i] != NULL);
        CHECK(((uintptr_t)pointers[i] & 15) == 0);
        if (i) CHECK(pointers[i] != pointers[i - 1]);
    }
    for (size_t i = 50; i > 0; --i) simpleos_reclaim_free(&heap, pointers[i - 1]);
    CHECK(heap.used == 0 && heap.last == NULL);
    return 0;
}

static int runtime_freestanding_check_frame_owners(void)
{
    runtime_freestanding_setup();
    unsigned char *retained = simpleos_reclaim_alloc(&heap, 256);
    CHECK(retained != NULL);
    memset(retained, 0x5a, 256);
    const size_t baseline = heap.used;
    /* Each frame owns its scratch; retained glyph/surface bytes are loans.
     * Freeing scratch in non-LIFO order must not rewind over retained data. */
    for (unsigned frame = 0; frame < 3000; ++frame) {
        unsigned char *pixels = simpleos_reclaim_alloc(&heap, 65536);
        unsigned char *scratch = simpleos_reclaim_alloc(&heap, 4096);
        CHECK(pixels && scratch);
        memset(pixels, (unsigned char)frame, 65536);
        memset(scratch, 0xa7, 4096);
        simpleos_reclaim_free(&heap, pixels);
        CHECK(scratch[0] == 0xa7 && scratch[4095] == 0xa7);
        simpleos_reclaim_free(&heap, scratch);
        CHECK(heap.used == baseline);
        CHECK(retained[0] == 0x5a && retained[255] == 0x5a);
    }
    simpleos_reclaim_free(&heap, retained);
    CHECK(heap.used == 0);
    return 0;
}

static int runtime_freestanding_check_coalescing(void)
{
    runtime_freestanding_setup();
    void *a = simpleos_reclaim_alloc(&heap, 64);
    void *b = simpleos_reclaim_alloc(&heap, 128);
    void *c = simpleos_reclaim_alloc(&heap, 256);
    unsigned char *d = simpleos_reclaim_alloc(&heap, 64);
    CHECK(a && b && c && d);
    memset(d, 0xc3, 64);
    size_t baseline = heap.used;
    simpleos_reclaim_free(&heap, b);
    simpleos_reclaim_free(&heap, c);
    void *merged = simpleos_reclaim_alloc(&heap, 352);
    CHECK(merged == b);
    CHECK(heap.used == baseline);
    void *split = simpleos_reclaim_alloc(&heap, 16);
    CHECK(split != NULL);
    CHECK(heap.used == baseline);
    CHECK(d[0] == 0xc3 && d[63] == 0xc3);
    simpleos_reclaim_free(&heap, merged);
    simpleos_reclaim_free(&heap, a);
    simpleos_reclaim_free(&heap, d);
    simpleos_reclaim_free(&heap, split);
    CHECK(heap.used == 0 && heap.last == NULL);
    for (unsigned i = 0; i < SIMPLEOS_HEAP_BINS; ++i) CHECK(heap.bins[i] == NULL);
    return 0;
}

static int runtime_freestanding_check_realloc(void)
{
    runtime_freestanding_setup();
    unsigned char *p = simpleos_reclaim_alloc(&heap, 256);
    CHECK(p != NULL);
    for (unsigned i = 0; i < 256; ++i) p[i] = (unsigned char)i;
    unsigned char *grown = simpleos_reclaim_realloc(&heap, p, 1024);
    CHECK(grown == p);
    for (unsigned i = 0; i < 256; ++i) CHECK(grown[i] == (unsigned char)i);
    void *guard = simpleos_reclaim_alloc(&heap, 32);
    CHECK(guard != NULL);
    unsigned char *moved = simpleos_reclaim_realloc(&heap, grown, 4096);
    CHECK(moved != NULL && moved != grown);
    for (unsigned i = 0; i < 256; ++i) CHECK(moved[i] == (unsigned char)i);
    size_t before = heap.used;
    CHECK(simpleos_reclaim_realloc(&heap, moved, SIZE_MAX) == NULL);
    CHECK(heap.used == before && moved[255] == 255);
    CHECK(simpleos_reclaim_realloc(&heap, moved, 64) == moved);
    CHECK(heap.used < before);
    CHECK(simpleos_reclaim_realloc(&heap, moved, 0) == NULL);
    simpleos_reclaim_free(&heap, guard);
    CHECK(heap.used == 0);
    CHECK(simpleos_reclaim_alloc(&heap, SIZE_MAX) == NULL);
    CHECK(simpleos_reclaim_alloc(&heap, sizeof(storage)) == NULL);
    CHECK(heap.used == 0);
    p = simpleos_reclaim_alloc(&heap, sizeof(storage) - sizeof(SimpleosHeapBlock));
    CHECK(p != NULL && heap.used == sizeof(storage));
    CHECK(simpleos_reclaim_alloc(&heap, 1) == NULL);
    CHECK(simpleos_reclaim_realloc(&heap, p, sizeof(storage)) == NULL);
    CHECK(heap.used == sizeof(storage));
    simpleos_reclaim_free(&heap, p);
    CHECK(heap.used == 0);
    return 0;
}

static int runtime_freestanding_check_mixed_owners(void)
{
    runtime_freestanding_setup();
    unsigned char *pointers[64] = {0};
    size_t lengths[64] = {0};
    uint32_t random = 0x12345678;
    for (unsigned step = 0; step < 20000; ++step) {
        random = random * 1664525u + 1013904223u;
        unsigned slot = (random >> 16) % 64;
        unsigned char pattern = (unsigned char)(slot + 1);
        if (pointers[slot]) {
            for (size_t i = 0; i < lengths[slot]; ++i) CHECK(pointers[slot][i] == pattern);
        }
        if (pointers[slot] && (random & 1)) {
            simpleos_reclaim_free(&heap, pointers[slot]);
            pointers[slot] = NULL;
        } else {
            size_t length = 1 + (random % 2048);
            unsigned char *next = simpleos_reclaim_realloc(&heap, pointers[slot], length);
            CHECK(next != NULL);
            if (pointers[slot]) {
                size_t preserved = lengths[slot] < length ? lengths[slot] : length;
                for (size_t i = 0; i < preserved; ++i) CHECK(next[i] == pattern);
            }
            pointers[slot] = next;
            lengths[slot] = length;
            memset(next, pattern, length);
        }
    }
    for (unsigned slot = 0; slot < 64; ++slot) {
        if (pointers[slot]) {
            for (size_t i = 0; i < lengths[slot]; ++i)
                CHECK(pointers[slot][i] == (unsigned char)(slot + 1));
            simpleos_reclaim_free(&heap, pointers[slot]);
        }
    }
    CHECK(heap.used == 0 && heap.last == NULL);
    return 0;
}

int main(void)
{
    if (runtime_freestanding_check_alignment() ||
        runtime_freestanding_check_frame_owners() ||
        runtime_freestanding_check_coalescing() ||
        runtime_freestanding_check_realloc() ||
        runtime_freestanding_check_mixed_owners()) return 1;
    printf("PASS simpleos reclaim heap: 5 scenarios, %u assertions\n", checks);
    return 0;
}
