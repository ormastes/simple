#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>

void* rt_struct_alloc(int64_t size);
int8_t rt_struct_receiver_valid(int64_t receiver, int64_t byte_offset, int64_t access_width);
void rt_free(void* ptr);
int32_t rt_transient_raw_scope_begin(void);
int32_t rt_transient_raw_scope_end(void);

#if defined(SIMPLE_RUNTIME_STRUCT_REGISTRY_TESTING)
int64_t rt_struct_registry_len(void);
int64_t rt_struct_registry_cap(void);
int64_t rt_struct_registry_failures(void);
#endif

enum {
    CONCURRENT_FREE_ROUNDS = 256,
    STRUCT_REGISTRY_GROWTH_ALLOCS = 384
};

typedef struct ConcurrentFreeState {
    _Atomic(uintptr_t) receiver;
    atomic_int phase;
} ConcurrentFreeState;

static void* concurrent_free_worker(void* opaque) {
    ConcurrentFreeState* state = (ConcurrentFreeState*)opaque;
    for (int round = 0; round < CONCURRENT_FREE_ROUNDS; round++) {
        while (atomic_load_explicit(&state->phase, memory_order_acquire) != 1) {
        }
        uintptr_t receiver = atomic_load_explicit(&state->receiver, memory_order_acquire);
        rt_free((void*)receiver);
        atomic_store_explicit(&state->phase, 2, memory_order_release);
        while (atomic_load_explicit(&state->phase, memory_order_acquire) != 3) {
        }
        atomic_store_explicit(&state->phase, 0, memory_order_release);
    }
    return NULL;
}

int main(void) {
    assert(rt_struct_alloc(-1) == NULL);
    int64_t* empty = (int64_t*)rt_struct_alloc(0);
    assert(empty == NULL);

    /* Exact regression: scope reclamation used to call libc free directly,
     * leaving this pointer admitted by the struct bounds registry. */
    assert(rt_transient_raw_scope_begin() == 1);
    int64_t* scoped = (int64_t*)rt_struct_alloc(16);
    assert(scoped != NULL);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)scoped, 8, 8) == 1);
    for (uintptr_t tag = 2; tag <= 7; tag++) {
        assert(rt_struct_receiver_valid(
            (int64_t)((uintptr_t)scoped | tag), 0, 8) == 0);
    }
    uintptr_t stale_scoped = (uintptr_t)scoped;
    assert(rt_transient_raw_scope_end() == 1);
    assert(rt_struct_receiver_valid((int64_t)stale_scoped, 0, 8) == 0);

    /* Adjacent explicit-free path must have the identical post-free result. */
    int64_t* explicit_receiver = (int64_t*)rt_struct_alloc(8);
    assert(explicit_receiver != NULL);
    uintptr_t stale_explicit = (uintptr_t)explicit_receiver;
    rt_free(explicit_receiver);
    assert(rt_struct_receiver_valid((int64_t)stale_explicit, 0, 8) == 0);

    /* Barrier-ordered cross-thread frees exercise the registry lock and prove
     * that publication of free completion never leaves an admitted pointer. */
    ConcurrentFreeState state;
    atomic_init(&state.receiver, 0);
    atomic_init(&state.phase, 0);
    pthread_t worker;
    assert(pthread_create(&worker, NULL, concurrent_free_worker, &state) == 0);
    for (int round = 0; round < CONCURRENT_FREE_ROUNDS; round++) {
        int64_t* receiver = (int64_t*)rt_struct_alloc(8);
        assert(receiver != NULL);
        assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver, 0, 8) == 1);
        atomic_store_explicit(&state.receiver, (uintptr_t)receiver, memory_order_release);
        atomic_store_explicit(&state.phase, 1, memory_order_release);
        while (atomic_load_explicit(&state.phase, memory_order_acquire) != 2) {
        }
        assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver, 0, 8) == 0);
        atomic_store_explicit(&state.phase, 3, memory_order_release);
        while (atomic_load_explicit(&state.phase, memory_order_acquire) != 0) {
        }
    }
    assert(pthread_join(worker, NULL) == 0);

    /* Cross the initial 256-slot table twice without a multi-million loop. */
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
    assert(rt_struct_registry_len() >= STRUCT_REGISTRY_GROWTH_ALLOCS);
    assert(rt_struct_registry_cap() > cap_before_growth);
    assert(rt_struct_registry_failures() == failures_before_growth);
#endif
    for (int i = 0; i < STRUCT_REGISTRY_GROWTH_ALLOCS; i++) rt_free(growth[i]);
    return 0;
}
