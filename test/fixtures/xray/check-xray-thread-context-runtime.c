/*
 * check-xray-thread-context-runtime.c
 * Exercises the real opt-in runtime_thread worker hooks against the real
 * Linux resident LLVM adapter. It is a bounded native C integration fixture,
 * not a Simple compiler/provider qualification test.
 */
#define _GNU_SOURCE 1
#include <pthread.h>
#include <sched.h>
#include <stdalign.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "runtime_thread.h"
#include "xray_resident_descriptor_v1.h"

enum XRayEntryType { XRAY_ENTRY = 0, XRAY_EXIT = 1, XRAY_TAIL = 2 };
enum XRayPatchingStatus { XRAY_NOT_INITIALIZED = 0, XRAY_SUCCESS = 1,
                          XRAY_ONGOING = 2, XRAY_FAILED = 3 };
typedef void (*xray_handler_fn)(int32_t, enum XRayEntryType);

static xray_handler_fn g_handler;
static int g_checks;
static int g_failures;

typedef struct {
    pthread_mutex_t lock;
    pthread_cond_t changed;
    unsigned arrived;
    uint64_t generation;
} TestBarrier;

static TestBarrier g_task_barrier;
static int64_t g_task_descriptor[2];
static _Atomic int g_writer_ready;
static _Atomic int g_writer_release;
static int64_t g_orphan_attach_status;

/* Memory-tracking scaffolding for the hosted worker object. The real
 * runtime_native.c object supplies the value and closure ABI owners. */
int g_memtrack_enabled = 0;
void spl_memtrack_record(void *ptr, int64_t size, const char *tag) {
    (void)ptr; (void)size; (void)tag;
}
void spl_memtrack_unrecord(void *ptr) { (void)ptr; }

/* Compiler-rt API stand-ins: the adapter registers its real handler here;
 * the test task invokes that exact function pointer with one mapped id. */
int __xray_set_handler(xray_handler_fn handler) {
    g_handler = handler;
    return handler != NULL;
}
enum XRayPatchingStatus __xray_patch_function(int32_t id) {
    (void)id; return XRAY_SUCCESS;
}
enum XRayPatchingStatus __xray_unpatch_function(int32_t id) {
    (void)id; return XRAY_SUCCESS;
}
size_t __xray_max_function_id(void) { return 1; }

int64_t simple_xray_resident_control_enter_v1(void);
void simple_xray_resident_control_leave_v1(void);
void simple_xray_resident_runtime_ready_v1(void);
int64_t simple_xray_thread_attach_v1(void);
void simple_xray_thread_detach_v1(void);
int64_t simple_xray_thread_task_root_v1(void);
int64_t simple_xray_llvm_resident_publish_v1(int64_t descriptor);
int64_t simple_xray_llvm_resident_close_v1(void);
int64_t simple_xray_llvm_resident_drained_v1(void);

#define CHECK(condition, message) do { \
    ++g_checks; \
    if (condition) printf("PASS %s\n", message); \
    else { printf("FAIL %s\n", message); ++g_failures; } \
} while (0)

#define REQUIRE(condition, message) do { \
    ++g_checks; \
    if (condition) printf("PASS %s\n", message); \
    else { printf("FAIL %s\n", message); ++g_failures; return 1; } \
} while (0)

#define TEST_CONTEXTS 4
#define TEST_CAPACITY 16
#define RT_POOL_TEST_DIRECT_MARKER INT64_C(0x5344495245435446)

typedef struct {
    SimpleXrayThreadContextHeaderV1 header;
    SimpleXrayThreadContextSlotV1 slots[TEST_CONTEXTS];
} TestContextPool;

typedef struct {
    SimpleXrayResidentDescriptorV1 descriptor;
    SimpleXrayResidentBindingV1 bindings[1];
    TestContextPool *pool;
    int64_t *arenas[TEST_CONTEXTS];
} TestSession;

static void *aligned_zero(size_t alignment, size_t bytes) {
    void *ptr = NULL;
    if (posix_memalign(&ptr, alignment, bytes) != 0) return NULL;
    memset(ptr, 0, bytes);
    return ptr;
}

static int test_barrier_init(TestBarrier *barrier) {
    memset(barrier, 0, sizeof(*barrier));
    if (pthread_mutex_init(&barrier->lock, NULL) != 0) return 0;
    if (pthread_cond_init(&barrier->changed, NULL) != 0) {
        pthread_mutex_destroy(&barrier->lock);
        return 0;
    }
    return 1;
}

static int test_barrier_wait(TestBarrier *barrier) {
    struct timespec deadline;
    if (clock_gettime(CLOCK_REALTIME, &deadline) != 0) return -1;
    deadline.tv_sec += 5;
    if (pthread_mutex_lock(&barrier->lock) != 0) return -1;
    uint64_t observed = barrier->generation;
    if (++barrier->arrived == 2) {
        barrier->arrived = 0;
        ++barrier->generation;
        pthread_cond_broadcast(&barrier->changed);
        pthread_mutex_unlock(&barrier->lock);
        return 0;
    }
    while (barrier->generation == observed) {
        int result = pthread_cond_timedwait(&barrier->changed, &barrier->lock, &deadline);
        if (result != 0) {
            if (barrier->generation == observed) {
                barrier->arrived = 0;
                ++barrier->generation;
                pthread_cond_broadcast(&barrier->changed);
            }
            pthread_mutex_unlock(&barrier->lock);
            return -1;
        }
    }
    pthread_mutex_unlock(&barrier->lock);
    return 0;
}

static void session_init(TestSession *session, uint64_t generation) {
    memset(session, 0, sizeof(*session));
    session->pool = aligned_zero(64, sizeof(TestContextPool));
    if (!session->pool) abort();
    session->pool->header.magic = SIMPLE_XRAY_THREAD_CONTEXT_MAGIC_V1;
    session->pool->header.schema = SIMPLE_XRAY_THREAD_CONTEXT_SCHEMA_V1;
    session->pool->header.actual_bytes = sizeof(TestContextPool);
    session->pool->header.max_slots = TEST_CONTEXTS;
    session->pool->header.generation = generation;
    session->pool->header.slots_offset = 64;

    size_t arena_bytes = 128 + TEST_CAPACITY * 96;
    for (size_t i = 0; i < TEST_CONTEXTS; ++i) {
        session->arenas[i] = aligned_zero(64, arena_bytes);
        if (!session->arenas[i]) abort();
        session->arenas[i][1] = (int64_t)generation;
        session->arenas[i][2] = (int64_t)(generation * 100 + i + 1);
        session->arenas[i][3] = TEST_CAPACITY;
        session->arenas[i][9] = (int64_t)arena_bytes;
        session->pool->slots[i].arena = (uint64_t)(uintptr_t)session->arenas[i];
        session->pool->slots[i].bytes = arena_bytes;
        session->pool->slots[i].context_id = generation * 100 + i + 1;
        session->pool->slots[i].state = SIMPLE_XRAY_THREAD_CONTEXT_UNUSED_V1;
    }

    session->bindings[0].llvm_id = 1;
    session->bindings[0].function_site = (UINT64_C(1) << 32) | 1u;
    session->descriptor.schema = 1;
    session->descriptor.actual_bytes = sizeof(SimpleXrayResidentDescriptorV1);
    session->descriptor.generation = generation;
    session->descriptor.module_instance = 1;
    session->descriptor.pool = (uint64_t)(uintptr_t)session->pool;
    session->descriptor.pool_bytes = sizeof(TestContextPool);
    session->descriptor.map = (uint64_t)(uintptr_t)session->bindings;
    session->descriptor.map_count = 1;
    session->descriptor.event_mask = 3;
}

static int64_t test_task(int64_t mode) {
    if (mode == 0) return 0; /* Pre-activation warmup keeps the worker alive. */
    if (test_barrier_wait(&g_task_barrier) != 0) return -9;
    if (mode < 0) return 0; /* Rendezvous proves both workers ran before activation. */
    if (mode == 3) {
        atomic_fetch_add_explicit(&g_writer_ready, 1, memory_order_release);
        while (!atomic_load_explicit(&g_writer_release, memory_order_acquire)) sched_yield();
        for (int i = 0; i < 1000; ++i)
            if (g_handler) g_handler(1, XRAY_ENTRY);
        return mode;
    }
    if (g_handler) {
        g_handler(1, XRAY_ENTRY);
        g_handler(1, XRAY_EXIT);
    }
    return mode;
}

static void *direct_thread_exit(void *unused) {
    (void)unused;
    if (g_handler) g_handler(1, XRAY_ENTRY);
    pthread_exit(NULL);
}

static int64_t submit_task(int64_t state, int64_t mode) {
    int64_t handle = rt_pool_state_try_submit_i64_kind_v1(
        state, 1, (int64_t)(intptr_t)g_task_descriptor, mode);
    if (handle <= 0) return handle;
    int64_t result = rt_pool_task_join_i64_v1(handle);
    if (rt_pool_task_release_i64_v1(handle) != 1) return -100;
    return result;
}

static int submit_pair(int64_t state, int64_t mode) {
    int64_t first = rt_pool_state_try_submit_i64_kind_v1(
        state, 1, (int64_t)(intptr_t)g_task_descriptor, mode);
    if (first <= 0) return 0;
    int64_t second = rt_pool_state_try_submit_i64_kind_v1(
        state, 1, (int64_t)(intptr_t)g_task_descriptor, mode);
    if (second <= 0) {
        (void)rt_pool_task_join_i64_v1(first); /* Timed rendezvous bounds cleanup. */
        (void)rt_pool_task_release_i64_v1(first);
        return 0;
    }
    int64_t first_result = rt_pool_task_join_i64_v1(first);
    int64_t second_result = rt_pool_task_join_i64_v1(second);
    int first_release = rt_pool_task_release_i64_v1(first) == 1;
    int second_release = rt_pool_task_release_i64_v1(second) == 1;
    int64_t expected = mode < 0 ? 0 : mode;
    return first_result == expected && second_result == expected && first_release && second_release;
}

static int submit_pair_async(int64_t state, int64_t mode, int64_t handles[2]) {
    handles[0] = rt_pool_state_try_submit_i64_kind_v1(
        state, 1, (int64_t)(intptr_t)g_task_descriptor, mode);
    if (handles[0] <= 0) return 0;
    handles[1] = rt_pool_state_try_submit_i64_kind_v1(
        state, 1, (int64_t)(intptr_t)g_task_descriptor, mode);
    if (handles[1] > 0) return 1;
    atomic_store_explicit(&g_writer_release, 1, memory_order_release);
    (void)rt_pool_task_join_i64_v1(handles[0]); /* Pair rendezvous is time bounded. */
    (void)rt_pool_task_release_i64_v1(handles[0]);
    return 0;
}

static int join_pair(int64_t handles[2], int64_t expected) {
    int64_t first = rt_pool_task_join_i64_v1(handles[0]);
    int64_t second = rt_pool_task_join_i64_v1(handles[1]);
    int released_first = rt_pool_task_release_i64_v1(handles[0]) == 1;
    int released_second = rt_pool_task_release_i64_v1(handles[1]) == 1;
    return first == expected && second == expected && released_first && released_second;
}

static int publish_session(TestSession *session) {
    if (simple_xray_resident_control_enter_v1() != 1) return 0;
    int64_t result = simple_xray_llvm_resident_publish_v1(
        (int64_t)(uintptr_t)&session->descriptor);
    simple_xray_resident_control_leave_v1();
    return result == 1;
}

static uint64_t count_context_events(TestSession *session, size_t slot_index,
                                    uint64_t wanted_context) {
    int64_t *arena = session->arenas[slot_index];
    int64_t write = __atomic_load_n(&arena[5], __ATOMIC_ACQUIRE);
    uint64_t count = 0;
    for (int64_t i = 0; i < write; ++i) {
        int64_t *record = arena + 16 + (i % TEST_CAPACITY) * 12;
        uint64_t kind = ((uint64_t)record[0] >> 32) & 0xffffu;
        if (record[1] == (int64_t)session->descriptor.generation &&
            record[4] == (int64_t)wanted_context && (kind == 1 || kind == 2))
            ++count;
    }
    return count;
}

static void *unattached_probe(void *raw) {
    (void)raw;
    g_orphan_attach_status = simple_xray_thread_attach_v1();
    if (g_handler) g_handler(1, XRAY_ENTRY);
    return NULL;
}

int main(void) {
    simple_xray_resident_runtime_ready_v1();
    REQUIRE(rt_pool_set_parallelism(2) == 2, "configure two persistent runtime_thread workers");
    int64_t state = rt_pool_state_create_v1(32);
    REQUIRE(state > 0, "create bounded runtime_thread state queue");
    REQUIRE(test_barrier_init(&g_task_barrier), "initialize bounded two-worker rendezvous");
    g_task_descriptor[0] = (int64_t)(intptr_t)test_task;
    g_task_descriptor[1] = RT_POOL_TEST_DIRECT_MARKER;
    REQUIRE(submit_task(state, 0) == 0, "pre-create pool workers before descriptor publication");
    REQUIRE(rt_pool_get_parallelism() == 2, "both pre-created workers remain available");
    REQUIRE(submit_pair(state, -1), "both pre-created workers run before descriptor publication");

    TestSession first;
    session_init(&first, 1);
    REQUIRE(publish_session(&first), "publish generation one through real adapter");
    REQUIRE(simple_xray_thread_attach_v1() == 1, "session owner attaches its thread context");
    REQUIRE(submit_pair(state, 1), "pre-created workers attach at task roots and emit events");
    REQUIRE(submit_pair(state, 1), "later task roots reuse the same thread slots");
    CHECK(first.pool->slots[0].state == 1 && first.pool->slots[1].state == 1 &&
          first.pool->slots[2].state == 1 && first.pool->slots[3].state == 0,
          "two persistent workers and owner use exactly three lifetime slots");
    CHECK(count_context_events(&first, 1, first.pool->slots[1].context_id) >= 4 &&
          count_context_events(&first, 2, first.pool->slots[2].context_id) >= 4,
          "worker events remain isolated in their per-thread arenas");

    REQUIRE(simple_xray_resident_control_enter_v1() == 1, "enter resident stop control");
    REQUIRE(simple_xray_llvm_resident_close_v1() == 1, "close generation one admission");
    simple_xray_resident_control_leave_v1();
    REQUIRE(simple_xray_llvm_resident_drained_v1() == 1, "generation one writers drained");
    simple_xray_thread_detach_v1();

    TestSession second;
    session_init(&second, 2);
    REQUIRE(publish_session(&second), "publish generation two after closed admission drains");
    REQUIRE(simple_xray_thread_attach_v1() == 1, "owner attaches generation two context");
    REQUIRE(submit_pair(state, 2), "pre-existing workers migrate at the next cold task roots");
    CHECK(first.pool->slots[0].state == SIMPLE_XRAY_THREAD_CONTEXT_DETACHED_V1 &&
          first.pool->slots[1].state == SIMPLE_XRAY_THREAD_CONTEXT_DETACHED_V1 &&
          first.pool->slots[2].state == SIMPLE_XRAY_THREAD_CONTEXT_DETACHED_V1,
          "old-generation worker and owner slots retire without reuse");
    CHECK(second.pool->slots[0].state == SIMPLE_XRAY_THREAD_CONTEXT_ATTACHED_V1 &&
          second.pool->slots[1].state == SIMPLE_XRAY_THREAD_CONTEXT_ATTACHED_V1 &&
          second.pool->slots[2].state == SIMPLE_XRAY_THREAD_CONTEXT_ATTACHED_V1,
          "generation two uses fresh bounded slots");
    CHECK(count_context_events(&second, 1, second.pool->slots[1].context_id) >= 2 &&
          count_context_events(&second, 2, second.pool->slots[2].context_id) >= 2,
          "generation two callbacks use migrated worker arenas");

    spl_thread_handle direct = spl_thread_create(direct_thread_exit, NULL);
    REQUIRE(direct != 0, "create an opt-in runtime_thread direct worker");
    REQUIRE(spl_thread_join(direct), "pthread_exit runs direct-worker cleanup");
    CHECK(second.pool->slots[3].state == SIMPLE_XRAY_THREAD_CONTEXT_DETACHED_V1 &&
          count_context_events(&second, 3, second.pool->slots[3].context_id) >= 1,
          "direct worker records in its arena and retires its slot on pthread_exit");

    pthread_t orphan;
    REQUIRE(pthread_create(&orphan, NULL, unattached_probe, NULL) == 0,
            "create an unattached foreign thread");
    REQUIRE(pthread_join(orphan, NULL) == 0, "join foreign thread");
    CHECK(g_orphan_attach_status == -2,
          "foreign attachment fails when all lifetime slots are exhausted");
    CHECK(second.pool->header.unattached_lost > 0,
          "unattached foreign-thread callback is counted and dropped");

    atomic_store_explicit(&g_writer_ready, 0, memory_order_relaxed);
    atomic_store_explicit(&g_writer_release, 0, memory_order_relaxed);
    int64_t racing_handles[2] = {0, 0};
    REQUIRE(submit_pair_async(state, 3, racing_handles),
            "start two active runtime_thread tasks for concurrent close");
    struct timespec ready_deadline;
    REQUIRE(clock_gettime(CLOCK_MONOTONIC, &ready_deadline) == 0,
            "read monotonic clock for bounded worker readiness");
    ready_deadline.tv_sec += 5;
    while (atomic_load_explicit(&g_writer_ready, memory_order_acquire) != 2) {
        struct timespec now;
        if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) {
            ++g_checks;
            ++g_failures;
            printf("FAIL read monotonic clock while waiting for active workers\n");
            return 1;
        }
        if (now.tv_sec > ready_deadline.tv_sec ||
            (now.tv_sec == ready_deadline.tv_sec && now.tv_nsec >= ready_deadline.tv_nsec))
            break;
        struct timespec pause = { .tv_sec = 0, .tv_nsec = 1000000 };
        (void)nanosleep(&pause, NULL);
    }
    REQUIRE(atomic_load_explicit(&g_writer_ready, memory_order_acquire) == 2,
            "both tasks reached the active-work gate before close");
    int64_t before_close[TEST_CONTEXTS];
    for (size_t i = 0; i < TEST_CONTEXTS; ++i)
        before_close[i] = __atomic_load_n(&second.arenas[i][5], __ATOMIC_ACQUIRE);
    REQUIRE(simple_xray_resident_control_enter_v1() == 1, "enter resident final stop control");
    REQUIRE(simple_xray_llvm_resident_close_v1() == 1,
            "close generation two while tasks are paused before callback attempts");
    simple_xray_resident_control_leave_v1();
    atomic_store_explicit(&g_writer_release, 1, memory_order_release);
    REQUIRE(join_pair(racing_handles, 3), "post-close callback attempts finish in active tasks");
    int post_close_unchanged = 1;
    for (size_t i = 0; i < TEST_CONTEXTS; ++i)
        if (__atomic_load_n(&second.arenas[i][5], __ATOMIC_ACQUIRE) != before_close[i])
            post_close_unchanged = 0;
    CHECK(post_close_unchanged,
          "callbacks attempted after close leave every generation-two arena unchanged");
    CHECK(simple_xray_llvm_resident_drained_v1() == 1, "generation two writers drained after close");
    simple_xray_thread_detach_v1();
    REQUIRE(rt_pool_state_close_v1(state) == 1, "close runtime_thread test queue");
    REQUIRE(rt_pool_state_join_idle_v1(state) == 1, "join runtime_thread state queue idle");
    REQUIRE(rt_pool_state_destroy_v1(state) == 1, "destroy runtime_thread test queue");
    (void)pthread_cond_destroy(&g_task_barrier.changed);
    (void)pthread_mutex_destroy(&g_task_barrier.lock);

    if (g_failures != 0) {
        printf("FAIL — %d of %d check(s)\n", g_failures, g_checks);
        return 1;
    }
    printf("PASS — %d check(s)\n", g_checks);
    return 0;
}
