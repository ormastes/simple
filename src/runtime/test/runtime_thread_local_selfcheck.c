#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../runtime_thread.c"

#define CHECK(c) do { if (!(c)) { \
    fprintf(stderr, "TLS check failed line %d: %s\n", __LINE__, #c); \
    exit(1); } } while (0)

static atomic_int phase;
static int64_t shared_handle;
static int64_t recycled_handle;
static void *worker(void *unused) {
    (void)unused;
    CHECK(rt_thread_local_get(shared_handle) == 0);
    rt_thread_local_set(shared_handle, INT64_MIN);
    CHECK(rt_thread_local_get(shared_handle) == INT64_MIN);
    atomic_store(&phase, 1);
    while (atomic_load(&phase) != 2) sched_yield();
    CHECK(rt_thread_local_get(shared_handle) == 0);
    rt_thread_local_set(shared_handle, 123);
    rt_thread_local_free(shared_handle);
    CHECK(rt_thread_local_get(recycled_handle) == 0);
    rt_thread_local_set(recycled_handle, -47);
    CHECK(rt_thread_local_get(recycled_handle) == -47);
    return NULL;
}

static void *racer(void *unused) {
    (void)unused;
    int64_t handle = shared_handle;
    atomic_store(&phase, 1);
    for (int i = 0; i < 100000; i++) {
        rt_thread_local_set(handle, -99);
        int64_t value = rt_thread_local_get(handle);
        CHECK(value == 0 || value == -99);
    }
    return NULL;
}

int main(int argc, char **argv) {
    if (argc > 1 && !strcmp(argv[1], "--negative-control")) {
        CHECK(!"intentional negative control");
    }
    CHECK(sizeof(g_tls_values) == 2048);
    int64_t invalid[] = {0, -1, INT64_MIN, INT64_MAX, 1};
    for (size_t i = 0; i < sizeof(invalid)/sizeof(invalid[0]); i++) {
        CHECK(rt_thread_local_get(invalid[i]) == 0);
        rt_thread_local_set(invalid[i], 8);
        rt_thread_local_free(invalid[i]);
    }
    shared_handle = rt_thread_local_new();
    CHECK(shared_handle > 0);
    CHECK(rt_thread_local_get(shared_handle) == 0);
    int64_t values[] = {0, 3, -1, INT64_MIN, INT64_MAX, 42, 0};
    for (size_t i = 0; i < sizeof(values)/sizeof(values[0]); i++) {
        rt_thread_local_set(shared_handle, values[i]);
        CHECK(rt_thread_local_get(shared_handle) == values[i]);
    }
    rt_thread_local_set(shared_handle, 42);
    pthread_t thread;
    CHECK(pthread_create(&thread, NULL, worker, NULL) == 0);
    while (atomic_load(&phase) != 1) sched_yield();
    CHECK(rt_thread_local_get(shared_handle) == 42);
    rt_thread_local_free(shared_handle);
    rt_thread_local_free(shared_handle);
    recycled_handle = rt_thread_local_new();
    CHECK(recycled_handle != shared_handle);
    CHECK(rt_thread_local_get(recycled_handle) == 0);
    rt_thread_local_set(recycled_handle, 81);
    atomic_store(&phase, 2);
    CHECK(pthread_join(thread, NULL) == 0);
    CHECK(rt_thread_local_get(recycled_handle) == 81);
    rt_thread_local_free(recycled_handle);

    int64_t slots[RT_TLS_SLOTS];
    for (int i = 0; i < RT_TLS_SLOTS; i++) {
        slots[i] = rt_thread_local_new(); CHECK(slots[i] > 0);
    }
    CHECK(rt_thread_local_new() == 0);
    for (int i = 0; i < RT_TLS_SLOTS; i++) rt_thread_local_free(slots[i]);
    for (int i = 0; i < 100000; i++) {
        int64_t h = rt_thread_local_new(); CHECK(h > 0);
        rt_thread_local_set(h, i);
        CHECK(rt_thread_local_get(h) == i);
        rt_thread_local_free(h); CHECK(rt_thread_local_get(h) == 0);
    }
    shared_handle = rt_thread_local_new();
    atomic_store(&phase, 0);
    CHECK(pthread_create(&thread, NULL, racer, NULL) == 0);
    while (atomic_load(&phase) != 1) sched_yield();
    rt_thread_local_free(shared_handle);
    int64_t replacement = rt_thread_local_new(); CHECK(replacement != shared_handle);
    rt_thread_local_set(replacement, 53);
    CHECK(pthread_join(thread, NULL) == 0);
    CHECK(rt_thread_local_get(replacement) == 53);
    rt_thread_local_free(replacement);
    /* Force the otherwise unreachable overflow boundary, without wrapping. */
    for (uint64_t i = 0; i < RT_TLS_SLOTS; i++)
        g_tls_generation[i] = ((uint64_t)INT64_MAX - i - 1) / RT_TLS_SLOTS;
    CHECK(rt_thread_local_new() == 0);
    g_tls_generation[RT_TLS_SLOTS - 1]--;
    int64_t last = rt_thread_local_new(); CHECK(last > 0);
    rt_thread_local_set(last, INT64_MAX);
    CHECK(rt_thread_local_get(last) == INT64_MAX);
    rt_thread_local_free(last);
    CHECK(rt_thread_local_new() == 0);
    puts("runtime TLS: PASS (raw i64, isolation, stale handles, capacity, retirement, concurrent free)");
    return 0;
}
