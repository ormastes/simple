#include "runtime.h"

#include <assert.h>
#include <stdint.h>

enum { STRUCT_REGISTRY_GROWTH_ALLOCS = 384 };

#if defined(SIMPLE_RUNTIME_STRUCT_REGISTRY_TESTING)
int64_t rt_struct_registry_len(void);
int64_t rt_struct_registry_cap(void);
int64_t rt_struct_registry_failures(void);
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
    return 0;
}
