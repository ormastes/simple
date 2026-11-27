#include "runtime.h"

#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

enum { STRUCT_REGISTRY_GROWTH_ALLOCS = 384 };

#if defined(SIMPLE_RUNTIME_STRUCT_REGISTRY_TESTING)
int64_t rt_struct_registry_len(void);
int64_t rt_struct_registry_cap(void);
int64_t rt_struct_registry_failures(void);
void rt_struct_registry_set_max_cap_for_test(size_t max_cap);
#endif

int main(void) {
    assert(rt_struct_alloc(-1) == NULL);
    int64_t* empty = (int64_t*)rt_struct_alloc(0);
    assert(empty == NULL);

    int64_t* receiver = (int64_t*)rt_struct_alloc(16);
    assert(receiver != NULL);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver, 0, 8) == 1);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver | 1, 8, 8) == 1);
    for (int tag = 2; tag <= 7; tag++) {
        assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver | tag, 0, 8) == 0);
    }
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver, 9, 8) == 0);
    assert(rt_struct_receiver_valid(INT64_C(0x1800000007), 0, 8) == 0);
    assert(rt_struct_receiver_valid(0, 0, 8) == 0);
    for (uintptr_t tag = 2; tag <= 7; tag++) {
        assert(rt_struct_receiver_valid(
            (int64_t)((uintptr_t)receiver | tag), 0, 8) == 0);
    }

    void* growth[STRUCT_REGISTRY_GROWTH_ALLOCS];
#if defined(SIMPLE_RUNTIME_STRUCT_REGISTRY_TESTING)
    int64_t cap_before_growth = rt_struct_registry_cap();
    int64_t failures_before_growth = rt_struct_registry_failures();
#endif
    for (int i = 0; i < STRUCT_REGISTRY_GROWTH_ALLOCS; i++) {
        growth[i] = rt_struct_alloc(8);
        assert(growth[i] != NULL);
    }
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)growth[0], 0, 8) == 1);
    assert(rt_struct_receiver_valid(
        (int64_t)(uintptr_t)growth[STRUCT_REGISTRY_GROWTH_ALLOCS - 1], 0, 8) == 1);
#if defined(SIMPLE_RUNTIME_STRUCT_REGISTRY_TESTING)
    assert(rt_struct_registry_len() >= STRUCT_REGISTRY_GROWTH_ALLOCS + 1);
    assert(rt_struct_registry_cap() > cap_before_growth);
    assert(rt_struct_registry_failures() == failures_before_growth);
#endif
    for (int i = 0; i < STRUCT_REGISTRY_GROWTH_ALLOCS; i++) rt_free(growth[i]);

    uintptr_t old_receiver = (uintptr_t)receiver;
    receiver = (int64_t*)rt_realloc(receiver, 24);
    assert(receiver != NULL);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver, 16, 8) == 1);
    if ((uintptr_t)receiver != old_receiver) {
        assert(rt_struct_receiver_valid((int64_t)old_receiver, 0, 8) == 0);
    }

    rt_free(receiver);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver, 0, 8) == 0);

#if defined(SIMPLE_RUNTIME_STRUCT_REGISTRY_TESTING)
    /* Verify tombstone compaction at the capacity ceiling preserves the empty
     * sentinel slot and bounds miss lookups without spinning. */
    size_t ceiling_cap = (size_t)rt_struct_registry_cap();
    assert(ceiling_cap >= 256);
    rt_struct_registry_set_max_cap_for_test(ceiling_cap);

    void* tomb_seed = rt_struct_alloc(16);
    assert(tomb_seed != NULL);
    size_t fill_count = ceiling_cap - 1 - (size_t)rt_struct_registry_len();
    void** fill = (void**)calloc(fill_count, sizeof(void*));
    assert(fill != NULL);
    for (size_t i = 0; i < fill_count; i++) {
        fill[i] = rt_struct_alloc(16);
        assert(fill[i] != NULL);
    }
    assert((size_t)rt_struct_registry_len() == ceiling_cap - 1);

    rt_free(tomb_seed);
    assert((size_t)rt_struct_registry_len() == ceiling_cap - 2);

    void* extra0 = rt_struct_alloc(16);
    assert(extra0 != NULL);
    assert((size_t)rt_struct_registry_len() == ceiling_cap - 1);

    int64_t failures_before_sat = rt_struct_registry_failures();
    void* extra1 = rt_struct_alloc(16);
    assert(extra1 == NULL);
    assert(rt_struct_registry_failures() == failures_before_sat + 1);
    assert(rt_struct_receiver_valid(INT64_C(0x1800000010), 0, 8) == 0);

    rt_free(extra0);
    for (size_t i = 0; i < fill_count; i++) rt_free(fill[i]);
    free(fill);
    rt_struct_registry_set_max_cap_for_test(0);
#endif
    return 0;
}
