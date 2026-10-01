#include "runtime_thread.h"

#include <inttypes.h>
#include <limits.h>
#include <pthread.h>
#include <stdio.h>

static int checks = 0;
static int failures = 0;

static void expect_i64(const char* name, int64_t actual, int64_t expected) {
    checks++;
    if (actual != expected) {
        fprintf(stderr, "FAIL %s: got %" PRId64 ", expected %" PRId64 "\n",
                name, actual, expected);
        failures++;
    }
}

typedef struct {
    int64_t first;
    int64_t second;
} WorkerArgs;

static void* worker(void* opaque) {
    WorkerArgs* args = (WorkerArgs*)opaque;
    expect_i64("worker first unset", rt_thread_local_get_i64(args->first), 0);
    expect_i64("worker second unset", rt_thread_local_get_i64(args->second), 0);
    rt_thread_local_set_i64(args->first, INT64_MIN);
    rt_thread_local_set_i64(args->second, -17);
    expect_i64("worker first full width", rt_thread_local_get_i64(args->first), INT64_MIN);
    expect_i64("worker second", rt_thread_local_get_i64(args->second), -17);
    return NULL;
}

int main(void) {
    int64_t first = rt_thread_local_new();
    int64_t second = rt_thread_local_new();
    expect_i64("first handle", first > 0, 1);
    expect_i64("second distinct handle", second > first, 1);
    if (first <= 0 || second <= 0) return 1;

    expect_i64("main first unset", rt_thread_local_get_i64(first), 0);
    expect_i64("main second unset", rt_thread_local_get_i64(second), 0);
    rt_thread_local_set_i64(first, INT64_MAX);
    rt_thread_local_set_i64(second, 23);
    expect_i64("main first full width", rt_thread_local_get_i64(first), INT64_MAX);
    expect_i64("main second", rt_thread_local_get_i64(second), 23);

    WorkerArgs args = {first, second};
    pthread_t thread;
    if (pthread_create(&thread, NULL, worker, &args) != 0 ||
        pthread_join(thread, NULL) != 0) {
        fprintf(stderr, "FAIL worker thread\n");
        return 1;
    }
    expect_i64("main first isolated", rt_thread_local_get_i64(first), INT64_MAX);
    expect_i64("main second isolated", rt_thread_local_get_i64(second), 23);

    rt_thread_local_free(first);
    expect_i64("freed read", rt_thread_local_get_i64(first), 0);
    rt_thread_local_set_i64(first, 9);
    expect_i64("freed set ignored", rt_thread_local_get_i64(first), 0);
    rt_thread_local_free(first);
    expect_i64("other key survives", rt_thread_local_get_i64(second), 23);

    int64_t third = rt_thread_local_new();
    expect_i64("public handle not recycled", third > second, 1);
    expect_i64("new key unset despite OS reuse", rt_thread_local_get_i64(third), 0);
    rt_thread_local_set_i64(third, INT64_MIN);
    expect_i64("new key stores negative extreme", rt_thread_local_get_i64(third), INT64_MIN);
    expect_i64("invalid zero", rt_thread_local_get_i64(0), 0);
    expect_i64("invalid negative", rt_thread_local_get_i64(-1), 0);
    expect_i64("invalid large", rt_thread_local_get_i64(INT64_MAX), 0);
    rt_thread_local_set_i64(INT64_MAX, 99);
    rt_thread_local_free(INT64_MAX);
    rt_thread_local_free(second);
    rt_thread_local_free(third);

    int64_t stale = third;
    for (int i = 0; i < 4096; i++) {
        int64_t fresh = rt_thread_local_new();
        if (fresh <= stale || rt_thread_local_get_i64(fresh) != 0) {
            fprintf(stderr, "FAIL slot reuse at iteration %d\n", i);
            return 1;
        }
        rt_thread_local_set_i64(fresh, i + 1);
        if (rt_thread_local_get_i64(fresh) != i + 1 ||
            rt_thread_local_get_i64(stale) != 0) {
            fprintf(stderr, "FAIL live/stale slot at iteration %d\n", i);
            return 1;
        }
        rt_thread_local_free(fresh);
        stale = fresh;
    }
    checks += 4096 * 3;

    if (checks < 20) return 1;
    if (failures) return 1;
    printf("PASS: C scalar TLS provider (%d checks)\n", checks);
    return 0;
}
