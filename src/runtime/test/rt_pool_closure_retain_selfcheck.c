/* PoolState v1 must keep a submitted closure alive until its task has run.
 *
 * A closure created inside a transient scope is freed when that scope ends.
 * The pool accepts closures (boxed entry, PR #4009); before it retained them,
 * a task that ran after the submitter's scope ended read a freed closure:
 * rt_closure_get_capture answered nil and the task returned a wrong value.
 *
 * Shape: one worker, blocked by a direct-record task; the closure task queues
 * behind it; the submitter's scope ends (dropping the only owner); then the
 * worker is released and the closure task runs late. Retains and releases are
 * counted: every retain is released exactly once, including a submit the
 * state refuses.
 *
 * Build (Linux), from src/runtime:
 *   cc -fsanitize=address -g -I. test/rt_pool_closure_retain_selfcheck.c \
 *      runtime_native.c runtime_thread.c runtime_memory.c ... -lpthread -lm -ldl
 * (the core-C composition objects; see build-core-c-bootstrap-runtime-capsule.shs) */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>

#include "../runtime.h"

extern int64_t rt_pool_set_parallelism(int64_t workers);
extern int64_t rt_pool_state_create_v1(int64_t capacity);
extern int64_t rt_pool_state_try_submit_i64_v1(int64_t state, int64_t entry, int64_t input);
extern int64_t rt_pool_task_join_i64_v1(int64_t task);
extern int64_t rt_pool_task_release_i64_v1(int64_t task);
extern int64_t rt_pool_state_close_v1(int64_t state);
extern int64_t rt_pool_state_destroy_v1(int64_t state);
extern int64_t rt_pool_state_pending_v1(int64_t state);
extern int64_t rt_pool_state_running_v1(int64_t state);
/* Weak so the pre-fix runtime still links; the fix must define it. */
extern void spl_closure_pin_stats(int64_t* retains, int64_t* releases, int64_t* live) __attribute__((weak));

#define DIRECT_MARKER INT64_C(0x5344495245435446)

static unsigned checks;
#define CHECK(x) do { ++checks; if (!(x)) { fprintf(stderr, "FAIL line=%d check=%u: %s\n", __LINE__, checks, #x); return 1; } } while (0)

static pthread_mutex_t gate_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t gate_cond = PTHREAD_COND_INITIALIZER;
static int gate_open;

static int64_t blocker_entry(int64_t input) {
    pthread_mutex_lock(&gate_lock);
    while (!gate_open) pthread_cond_wait(&gate_cond, &gate_lock);
    pthread_mutex_unlock(&gate_lock);
    return input;
}

/* Boxed-entry convention: (closure, tagged...) -> tagged. */
static int64_t add_capture_boxed(int64_t closure, int64_t tagged) {
    int64_t capture = rt_closure_get_capture(closure, 0);
    return rt_value_int(rt_value_unbox_int(tagged) + rt_value_unbox_int(capture));
}

static void pin_stats(int64_t* retains, int64_t* releases, int64_t* live) {
    *retains = *releases = *live = -1;
    if (spl_closure_pin_stats) spl_closure_pin_stats(retains, releases, live);
}

int main(void) {
    static int64_t blocker[2];
    blocker[0] = (int64_t)(uintptr_t)blocker_entry;
    blocker[1] = DIRECT_MARKER;

    CHECK(rt_pool_set_parallelism(1) >= 0);
    int64_t state = rt_pool_state_create_v1(2);
    CHECK(state != 0);

    int64_t block_task = rt_pool_state_try_submit_i64_v1(state, (int64_t)(uintptr_t)blocker, 1);
    CHECK(block_task > 0);
    /* Wait until the only worker is inside the blocker, so the closure task
     * cannot run before the submitter's scope ends. */
    int spin = 0;
    while (rt_pool_state_running_v1(state) != 1 && spin < 200000000) spin++;
    CHECK(rt_pool_state_running_v1(state) == 1);

    CHECK(rt_transient_array_scope_begin() == 1);
    int64_t closure = rt_closure_new((int64_t)(uintptr_t)add_capture_boxed, 1);
    CHECK(rt_closure_func_ptr(closure) != 0);
    CHECK(rt_closure_set_capture(closure, 0, rt_value_int(7)) == 1);
    int64_t closure_task = rt_pool_state_try_submit_i64_v1(state, closure, 5);
    CHECK(closure_task > 0);
    CHECK(rt_pool_state_pending_v1(state) == 1); /* queued behind the blocker */
    /* Capacity 2 is now full: a refused submit must not keep its retain. */
    CHECK(rt_pool_state_try_submit_i64_v1(state, closure, 9) == -1);
    /* The submitter drops its only owner: the scope frees what it allocated. */
    CHECK(rt_transient_array_scope_end() == 1);

    pthread_mutex_lock(&gate_lock);
    gate_open = 1;
    pthread_cond_broadcast(&gate_cond);
    pthread_mutex_unlock(&gate_lock);

    CHECK(rt_pool_task_join_i64_v1(block_task) == 1);
    int64_t result = rt_pool_task_join_i64_v1(closure_task);
    fprintf(stderr, "closure task result=%lld (want 12)\n", (long long)result);
    CHECK(result == 12);
    CHECK(rt_pool_task_release_i64_v1(block_task) == 1);
    CHECK(rt_pool_task_release_i64_v1(closure_task) == 1);

    int64_t retains, releases, live;
    pin_stats(&retains, &releases, &live);
    fprintf(stderr, "closure pins: retains=%lld releases=%lld live=%lld\n",
            (long long)retains, (long long)releases, (long long)live);
    CHECK(retains == 2); /* accepted submit + refused submit */
    CHECK(releases == retains);
    CHECK(live == 0);
    /* The scope ended while pinned, so the last release freed it: no leak. */
    CHECK(rt_closure_func_ptr(closure) == 0);
    CHECK(rt_closure_release(closure) == 0); /* no pin left: never a double free */

    CHECK(rt_pool_state_close_v1(state) == 1);
    CHECK(rt_pool_state_destroy_v1(state) == 1);
    printf("SELFCHECK PASSED (0 failures)\n");
    return 0;
}
