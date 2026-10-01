#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <sched.h>
#include "../../../src/runtime/runtime_mcdc_v1.h"

static _Atomic int pause_after_load;
static _Atomic int target_captured;
static _Atomic int target_calls;

void simple_mcdc_dynamic_race_test_after_target_load(void) {
    if (!atomic_load_explicit(&pause_after_load, memory_order_acquire)) return;
    atomic_store_explicit(&target_captured, 1, memory_order_release);
    while (atomic_load_explicit(&pause_after_load, memory_order_acquire))
        sched_yield();
}

static int32_t counted_target(uint64_t decision_id, uint32_t condition_count,
                              uint64_t source_digest, uint64_t evaluated_mask,
                              uint64_t true_mask, uint8_t outcome) {
    (void)decision_id; (void)condition_count; (void)source_digest;
    (void)evaluated_mask; (void)true_mask; (void)outcome;
    atomic_fetch_add_explicit(&target_calls, 1, memory_order_relaxed);
    return 0;
}

static uint64_t target_address(void) {
    uintptr_t raw = 0;
    SimpleMcdcDynamicTargetV1 target = counted_target;
    assert(sizeof(target) <= sizeof(raw));
    __builtin_memcpy(&raw, &target, sizeof(target));
    return (uint64_t)raw;
}

static void *reader(void *unused) {
    (void)unused;
    assert(rt_mcdc_dynamic_vector_patchpoint_v1(1, 1, 1, 1, 1, 1) == 0);
    return NULL;
}

/* Focused link dependency; report conversion is not exercised. */
int64_t rt_string_new(const uint8_t *bytes, uint64_t len) {
    (void)bytes; (void)len; return 0;
}

int main(void) {
    const uint64_t owner = 991;
    const uint64_t handle =
        rt_mcdc_dynamic_register_target_v1(target_address(), owner);
    assert(handle > 1);
    assert(rt_mcdc_dynamic_bind_v1(handle) == 0);

    atomic_store_explicit(&pause_after_load, 1, memory_order_release);
    pthread_t thread;
    assert(pthread_create(&thread, NULL, reader, NULL) == 0);
    while (!atomic_load_explicit(&target_captured, memory_order_acquire))
        sched_yield();

    /* Negative control: the reader has captured the formerly callable target,
     * but owns no lease yet. Unbind may settle immediately; revalidation must
     * suppress that stale call after the test releases the race window. */
    assert(rt_mcdc_dynamic_unbind_v1(handle) == 0);
    assert(rt_mcdc_dynamic_settled_v1() == 0);
    atomic_store_explicit(&pause_after_load, 0, memory_order_release);
    assert(pthread_join(thread, NULL) == 0);
    assert(atomic_load_explicit(&target_calls, memory_order_relaxed) == 0);

    assert(rt_mcdc_dynamic_bind_v1(handle) == 0);
    assert(rt_mcdc_dynamic_vector_patchpoint_v1(1, 1, 1, 1, 1, 1) == 0);
    assert(atomic_load_explicit(&target_calls, memory_order_relaxed) == 1);
    assert(rt_mcdc_dynamic_unbind_v1(handle) == 0);
    assert(rt_mcdc_dynamic_unregister_target_v1(handle, owner) == 0);
    puts("PASS staged_stale_capture=1 stale_target_calls=0 armed_target_calls=1");
    return 0;
}
