#ifndef SIMPLE_XRAY_RESIDENT_DESCRIPTOR_V1_H
#define SIMPLE_XRAY_RESIDENT_DESCRIPTOR_V1_H

#include <stddef.h>
#include <stdint.h>
#include "xray_thread_context_v1.h"

/* Private wire layout, initialized only by the trusted resident provider from
 * its own retained allocations. Shape validation is not pointer authority. */
typedef struct {
    uint64_t llvm_id;
    uint64_t function_site;
} SimpleXrayResidentBindingV1;

typedef struct {
    uint64_t schema;
    uint64_t actual_bytes;
    uint64_t generation;
    uint64_t module_instance;
    uint64_t pool;
    uint64_t pool_bytes;
    uint64_t map;
    uint64_t map_count;
    uint64_t event_mask;
    uint64_t reserved_zero;
} SimpleXrayResidentDescriptorV1;

_Static_assert(sizeof(SimpleXrayResidentDescriptorV1) == 80, "resident descriptor size");
_Static_assert(offsetof(SimpleXrayResidentDescriptorV1, pool) == 32, "resident pool offset");
_Static_assert(offsetof(SimpleXrayResidentDescriptorV1, map) == 48, "resident map offset");
_Static_assert(offsetof(SimpleXrayResidentDescriptorV1, event_mask) == 64, "resident mask offset");
_Static_assert(sizeof(SimpleXrayResidentBindingV1) == 16, "resident binding size");

static inline const SimpleXrayResidentBindingV1 *simple_xray_resident_find_v1(
        const SimpleXrayResidentDescriptorV1 *descriptor, uint64_t id) {
    const SimpleXrayResidentBindingV1 *rows =
        (const SimpleXrayResidentBindingV1 *)(uintptr_t)descriptor->map;
    uint64_t low = 0, high = descriptor->map_count;
    /* count is validated <=4096 before publication: at most13 comparisons. */
    while (low < high) {
        uint64_t middle = low + (high - low) / 2;
        if (rows[middle].llvm_id < id) low = middle + 1;
        else high = middle;
    }
    return low < descriptor->map_count && rows[low].llvm_id == id ? &rows[low] : NULL;
}

#endif
