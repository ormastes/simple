/* Host execution of the production x86 ABI slice, inserted by abi_probe_run.shs.
 * No kernel, native compiler, or VM is required. */
#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef uint64_t RuntimeValue;
static _Alignas(16) uint8_t test_heap[4096];
static size_t test_offset;
static void *abi_test_malloc(size_t bytes)
{
    size_t aligned = (bytes + 15u) & ~(size_t)15u;
    assert(aligned <= sizeof(test_heap) - test_offset);
    void *result = test_heap + test_offset;
    test_offset += aligned;
    return result;
}
#define malloc abi_test_malloc
/* PRODUCTION_RUNTIME_SLICE */
#undef malloc

/* Retained for machine-code review: canonical initialization must stay one
 * fixed-width metadata store, without loops, allocation, or external calls. */
void abi_header_init_codegen(HeapHeader *header)
{
    runtime_heap_header_init(header, HEAP_ARRAY);
}

int main(void)
{
    memset(test_heap, 0xff, sizeof(test_heap));
    const uint8_t banner[] = {'S', 'S', 'H', '-', '2', '.', '0', '-'};
    RuntimeArray *packed = runtime_array_from_abi(_rt_bytes_new(banner, sizeof(banner)));
    assert(packed && packed->hdr.type == HEAP_ARRAY);
    assert(packed->hdr.gc_flags == BYTE_PACKED && packed->hdr.reserved == 0);
    assert(packed->hdr.size == sizeof(RuntimeArray) + sizeof(banner));
    for (uint32_t i = 0; i < sizeof(banner); ++i)
        assert(_rt_bytes_get(packed, i) == banner[i]);

    /* Reuse a packed allocation with nonzero reserved bytes as a slot array.
     * Before the fix its stale BYTE_PACKED flag changes the element stride. */
    packed->hdr.reserved = UINT16_MAX;
    test_offset = 0;
    RuntimeArray *slots = runtime_array_from_abi(rt_u32_alloc_filled(8, 0));
    assert(slots == packed);
    assert(slots->hdr.gc_flags == 0 && slots->hdr.reserved == 0);
    assert(slots->hdr.size == sizeof(RuntimeArray) + 8 * sizeof(RuntimeValue));
    for (uint32_t i = 0; i < sizeof(banner); ++i) {
        slots->items[i] = ENCODE_INT(banner[i]);
        assert(_rt_bytes_get(slots, i) == banner[i]);
    }
    _rt_bytes_set(slots, 3, 255);
    assert(slots->items[3] == ENCODE_INT(255));
    assert(_rt_bytes_get(slots, 3) == 255);

    /* Repeat poisoned reuse for every object tag; packed producers alone set
     * BYTE_PACKED after the common initialization. Size belongs to callers. */
    /* 8..13 cover the sibling-TU generator/shared/unique/weak/future/builder,
     * BTree, and hash constructors (some families intentionally share tags). */
    for (uint8_t tag = HEAP_STRING; tag <= 13; ++tag) {
        HeapHeader header = {255, 255, UINT16_MAX, 0x12345678};
        runtime_heap_header_init(&header, tag);
        assert(header.type == tag && header.gc_flags == 0 && header.reserved == 0);
        assert(header.size == 0x12345678);
    }
    puts("PASS x64 SSH ABI packed/slot poisoned-reuse and sibling heap-header tags");
    return 0;
}
