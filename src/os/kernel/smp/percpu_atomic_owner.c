#include <stdbool.h>
#include <stdint.h>

/* CPU 0 is the BSP and is online before AP startup begins. */
static uint32_t simpleos_online_mask = 1u;

void rt_simpleos_percpu_online_reset(void) {
    __atomic_store_n(&simpleos_online_mask, 1u, __ATOMIC_RELEASE);
}

uint32_t rt_simpleos_percpu_online_count(void) {
    uint32_t mask = __atomic_load_n(&simpleos_online_mask, __ATOMIC_ACQUIRE);
    return (uint32_t)__builtin_popcount(mask);
}

bool rt_simpleos_percpu_mark_online(uint32_t cpu_id) {
    if (cpu_id >= 32u) return false;
    uint32_t bit = 1u << cpu_id;
    uint32_t old = __atomic_fetch_or(&simpleos_online_mask, bit, __ATOMIC_ACQ_REL);
    return (old & bit) == 0u;
}

bool rt_simpleos_percpu_is_online(uint32_t cpu_id) {
    if (cpu_id >= 32u) return false;
    uint32_t mask = __atomic_load_n(&simpleos_online_mask, __ATOMIC_ACQUIRE);
    return (mask & (1u << cpu_id)) != 0u;
}

#ifdef SIMPLEOS_PERCPU_ATOMIC_SELF_TEST
#include <assert.h>
#include <pthread.h>

static void *mark_all(void *unused) {
    (void)unused;
    for (uint32_t pass = 0; pass < 1000u; pass++) {
        for (uint32_t cpu = 1u; cpu < 32u; cpu++)
            (void)rt_simpleos_percpu_mark_online(cpu);
    }
    return 0;
}

int main(void) {
    pthread_t threads[16];
    rt_simpleos_percpu_online_reset();
    for (uint32_t i = 0; i < 16u; i++)
        assert(pthread_create(&threads[i], 0, mark_all, 0) == 0);
    for (uint32_t i = 0; i < 16u; i++)
        assert(pthread_join(threads[i], 0) == 0);
    assert(rt_simpleos_percpu_online_count() == 32u);
    assert(rt_simpleos_percpu_is_online(0u));
    assert(rt_simpleos_percpu_is_online(31u));
    assert(!rt_simpleos_percpu_is_online(32u));
    assert(!rt_simpleos_percpu_mark_online(32u));
    return 0;
}
#endif
