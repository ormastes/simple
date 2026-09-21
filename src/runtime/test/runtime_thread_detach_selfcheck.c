#include <stdio.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "../runtime_memtrack.h"

/* Runtime checks must survive release CFLAGS such as -DNDEBUG. */
#define CHECK(condition) do { \
    if (!(condition)) { \
        fprintf(stderr, "thread detach check failed at line %d: %s\n", \
                __LINE__, #condition); \
        exit(EXIT_FAILURE); \
    } \
} while (0)

/* Observe real allocation/free while running the production thread provider. */
static atomic_int records_live;
static void *record;
static void *observed_malloc(size_t size, const char *tag) {
    void *ptr = malloc(size);
    if (ptr && (!strcmp(tag, "rt_thread") || !strcmp(tag, "rt_thread2"))) {
        record = ptr;
        atomic_fetch_add(&records_live, 1);
    }
    return ptr;
}
static void observed_free(void *ptr) {
    int is_record = ptr == record;
    free(ptr);
    if (is_record) atomic_fetch_sub(&records_live, 1);
}
#undef SPL_MALLOC
#undef SPL_FREE
#define SPL_MALLOC(size, tag) observed_malloc(size, tag)
#define SPL_FREE(ptr) observed_free(ptr)
#ifndef THREAD_PROVIDER_SOURCE
#define THREAD_PROVIDER_SOURCE "../runtime_thread.c"
#endif
#include THREAD_PROVIDER_SOURCE

void worker_loop_entry(int64_t pool_id) {
    (void)pool_id;
    CHECK(!"this probe does not start pool workers");
}

static atomic_int entered;
static atomic_int proceed;
static void wait_for(atomic_int *value, int expected) {
    struct timespec pause = {0, 1000000};
    for (int i = 0; i < 5000; i++) {
        if (atomic_load(value) == expected) return;
        nanosleep(&pause, NULL);
    }
    CHECK(!"thread lifetime probe timed out");
}
static int64_t blocked_worker(int64_t closure) {
    (void)closure;
    atomic_store(&entered, 1);
    wait_for(&proceed, 1);
    return 42;
}
static int64_t blocked_worker2(int64_t one, int64_t two) {
    blocked_worker(0);
    return one + two;
}
int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1], "--negative-control")) {
        CHECK(!"intentional negative control");
    }
    spl_thread_init();
    for (int variant = 0; variant < 4; variant++) {
        atomic_store(&entered, 0);
        atomic_store(&proceed, 0);
        int64_t closure[] = {(int64_t)(intptr_t)blocked_worker, 0};
        int64_t closure2[] = {(int64_t)(intptr_t)blocked_worker2,
                             RT_NATIVE_DIRECT_FUNCTION_RECORD_MARKER};
        int64_t handle = variant == 1
            ? rt_thread_spawn_isolated_with_args((int64_t)(intptr_t)closure2, 16, 26)
            : rt_thread_spawn_isolated((int64_t)(intptr_t)closure, 0);
        CHECK(handle > 0);
        wait_for(&entered, 1);
        CHECK(rt_thread_is_done(handle) == 0);
        if (variant < 2) {
            rt_thread_free(handle);
            /* The worker must retain its own record after handle release. */
            CHECK(atomic_load(&records_live) == 1);
            atomic_store(&proceed, 1);
        } else if (variant == 2) {
            atomic_store(&proceed, 1);
            int64_t result = rt_thread_join(handle);
            CHECK(result == 42);
        } else {
            atomic_store(&proceed, 1);
            RtThreadData *td = get_handle(handle, HANDLE_THREAD);
            wait_for(&td->done, 1);
            CHECK(rt_thread_is_done(handle) == 1);
            rt_thread_free(handle);
        }
        wait_for(&records_live, 0);
        CHECK(rt_thread_is_done(handle) == 1);
        switch (variant) {
            case 0: puts("detach_isolated: worker_completed record_reclaimed"); break;
            case 1: puts("detach_with_args: worker_completed record_reclaimed"); break;
            case 2: puts("join: result=42 record_reclaimed"); break;
            case 3: puts("detach_completed: record_reclaimed"); break;
        }
    }
    /* Exhaust admission after native creation; failure must release its share. */
    int64_t handles[MAX_HANDLES - 1];
    for (int i = 0; i < MAX_HANDLES - 1; i++) {
        handles[i] = alloc_handle(HANDLE_MUTEX, &handles[i]);
        CHECK(handles[i] > 0);
    }
    atomic_store(&entered, 0);
    atomic_store(&proceed, 0);
    int64_t closure[] = {(int64_t)(intptr_t)blocked_worker, 0};
    int64_t rejected = rt_thread_spawn_isolated((int64_t)(intptr_t)closure, 0);
    CHECK(rejected == 0);
    wait_for(&entered, 1);
    CHECK(atomic_load(&records_live) == 1);
    atomic_store(&proceed, 1);
    wait_for(&records_live, 0);
    for (int i = 0; i < MAX_HANDLES - 1; i++) free_handle(handles[i]);
    puts("handle_exhaustion: worker_completed record_reclaimed");
    puts("runtime thread detach selfcheck: PASS");
    return 0;
}
