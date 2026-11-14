/*
 * check-xray-thread-context.c
 * Focused C fixture checking selected pin and TLS-slot behaviors in the
 * production thread-context and resident-admission headers. It does not claim
 * the optional runtime_thread hooks are enabled by this fixture.
 * `xray_resident_admission_v1.h` is included unchanged from provider commit
 * 496aa866383; the thread-context header is owned on this fixture branch.
 */
#include <pthread.h>
#include <stdalign.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../../../src/runtime/xray/xray_resident_admission_v1.h"
#include "../../../src/runtime/xray/xray_thread_context_v1.h"

#define REQUIRE(condition) do { \
    if (!(condition)) { \
        fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #condition); \
        return 1; \
    } \
} while (0)

typedef struct {
    SimpleXrayThreadContextHeaderV1 header;
    SimpleXrayThreadContextSlotV1 slots[3];
} TestContextTable;

_Static_assert(offsetof(TestContextTable, slots) == 64,
               "test context slots must begin at byte 64");

typedef struct {
    alignas(8) TestContextTable table;
    alignas(8) int64_t arenas[3][16];
    simple_xray_resident_admission_v1 admission;
} TestPool;

static TestPool g_pool_a;
static TestPool g_pool_b;
static uint64_t g_thread_arenas[2];
static int g_thread_status[2];
static int g_exhaust_status;
static pthread_barrier_t g_attach_barrier;

static void init_pool(TestPool *pool, uint64_t generation, uint64_t max_slots) {
    memset(pool, 0, sizeof(*pool));
    SimpleXrayThreadContextHeaderV1 *header = &pool->table.header;
    header->magic = SIMPLE_XRAY_THREAD_CONTEXT_MAGIC_V1;
    header->schema = SIMPLE_XRAY_THREAD_CONTEXT_SCHEMA_V1;
    header->actual_bytes = 64u + max_slots * 32u;
    header->max_slots = max_slots;
    header->generation = generation;
    header->slots_offset = 64u;
    for (uint64_t i = 0; i < max_slots; ++i) {
        pool->table.slots[i].arena = (uint64_t)(uintptr_t)pool->arenas[i];
        pool->table.slots[i].bytes = sizeof(pool->arenas[i]);
        pool->table.slots[i].context_id = generation * 100u + i + 1u;
        __atomic_store_n(&pool->table.slots[i].state, SIMPLE_XRAY_THREAD_CONTEXT_UNUSED_V1,
                         __ATOMIC_RELAXED);
    }
    atomic_init(&pool->admission.gate, UINT64_C(1));
    atomic_init(&pool->admission.descriptor, NULL);
    if (!simple_xray_resident_publish_v1(&pool->admission, header)) abort();
}

static void *attach_worker(void *raw_index) {
    uintptr_t index = (uintptr_t)raw_index;
    TestPool *pool = &g_pool_a;
    SimpleXrayThreadContextHeaderV1 *header = &pool->table.header;
    (void)pthread_barrier_wait(&g_attach_barrier);
    void *descriptor = simple_xray_resident_acquire_v1(&pool->admission);
    if (descriptor != header) {
        g_thread_status[index] = 10;
        if (descriptor != NULL)
            simple_xray_resident_release_v1(&pool->admission);
        return NULL;
    }
    int64_t first = simple_xray_thread_attach_pool_v1(descriptor, sizeof(pool->table));
    int64_t second = simple_xray_thread_attach_pool_v1(descriptor, sizeof(pool->table));
    int64_t arena = simple_xray_thread_current_arena_v1(descriptor);
    int64_t stale = simple_xray_thread_current_arena_v1(&g_pool_b.table.header);
    if (first != 1 || second != 1 || arena <= 0 || stale != 0) {
        g_thread_status[index] = 11;
        simple_xray_thread_detach_pool_v1();
        simple_xray_resident_release_v1(&pool->admission);
        return NULL;
    }
    g_thread_arenas[index] = (uint64_t)arena;
    g_thread_status[index] = (int)simple_xray_thread_detach_pool_v1();
    simple_xray_resident_release_v1(&pool->admission);
    return NULL;
}

static void *exhaust_worker(void *unused) {
    (void)unused;
    TestPool *pool = &g_pool_b;
    void *descriptor = simple_xray_resident_acquire_v1(&pool->admission);
    if (descriptor == NULL) {
        g_exhaust_status = -10;
        return NULL;
    }
    g_exhaust_status = (int)simple_xray_thread_attach_pool_v1(
        descriptor, sizeof(pool->table));
    simple_xray_resident_release_v1(&pool->admission);
    return NULL;
}

int main(void) {
    init_pool(&g_pool_a, 7, 3);
    init_pool(&g_pool_b, 8, 1);
    REQUIRE(pthread_barrier_init(&g_attach_barrier, NULL, 2) == 0);

    /* Two independent OS threads attach to one immutable table, get different
     * preallocated arenas, and exercise same-pool idempotence. */
    pthread_t threads[2];
    REQUIRE(pthread_create(&threads[0], NULL, attach_worker, (void *)(uintptr_t)0) == 0);
    REQUIRE(pthread_create(&threads[1], NULL, attach_worker, (void *)(uintptr_t)1) == 0);
    REQUIRE(pthread_join(threads[0], NULL) == 0);
    REQUIRE(pthread_join(threads[1], NULL) == 0);
    REQUIRE(g_thread_status[0] == 1 && g_thread_status[1] == 1);
    REQUIRE(g_thread_arenas[0] != 0 && g_thread_arenas[1] != 0);
    REQUIRE(g_thread_arenas[0] != g_thread_arenas[1]);
    REQUIRE(pthread_barrier_destroy(&g_attach_barrier) == 0);

    /* Slot state 2 is retired, never reused. A new attachment on pool A uses
     * the last slot; cross-pool attachment while already attached fails. */
    SimpleXrayThreadContextHeaderV1 *header_a = &g_pool_a.table.header;
    void *descriptor_a = simple_xray_resident_acquire_v1(&g_pool_a.admission);
    REQUIRE(descriptor_a == header_a);
    REQUIRE(simple_xray_thread_attach_pool_v1(descriptor_a, sizeof(g_pool_a.table)) == 1);
    void *descriptor_b = simple_xray_resident_acquire_v1(&g_pool_b.admission);
    REQUIRE(descriptor_b != NULL);
    REQUIRE(simple_xray_thread_attach_pool_v1(descriptor_b, sizeof(g_pool_b.table)) == -4);
    simple_xray_resident_release_v1(&g_pool_b.admission);
    REQUIRE(simple_xray_thread_detach_pool_v1() == 1);
    simple_xray_resident_release_v1(&g_pool_a.admission);

    /* Pool B has one lifetime slot; after detach, another thread cannot reuse
     * it. The failed attempt is explicit and does not attach implicitly. */
    void *descriptor_b2 = simple_xray_resident_acquire_v1(&g_pool_b.admission);
    REQUIRE(descriptor_b2 != NULL);
    REQUIRE(simple_xray_thread_attach_pool_v1(descriptor_b2, sizeof(g_pool_b.table)) == 1);
    REQUIRE(simple_xray_thread_detach_pool_v1() == 1);
    simple_xray_resident_release_v1(&g_pool_b.admission);
    pthread_t exhausted;
    REQUIRE(pthread_create(&exhausted, NULL, exhaust_worker, NULL) == 0);
    REQUIRE(pthread_join(exhausted, NULL) == 0);
    REQUIRE(g_exhaust_status == -2);

    /* Invalid extent/schema fails closed before slot access. */
    TestContextTable bad_schema = g_pool_b.table;
    bad_schema.header.schema = 0;
    REQUIRE(simple_xray_thread_attach_pool_v1(&bad_schema, sizeof(bad_schema)) == -3);
    REQUIRE(simple_xray_thread_attach_pool_v1(header_a, 63) == -3);

    /* The counter is exact below the sentinel and sticky-inexact at UINT64_MAX. */
    for (int i = 0; i < 12; ++i)
        simple_xray_thread_note_unattached_v1(header_a);
    REQUIRE(__atomic_load_n(&header_a->unattached_lost, __ATOMIC_RELAXED) == 12);
    __atomic_store_n(&header_a->unattached_lost, UINT64_MAX - 1u, __ATOMIC_RELAXED);
    simple_xray_thread_note_unattached_v1(header_a);
    REQUIRE(__atomic_load_n(&header_a->unattached_lost, __ATOMIC_RELAXED) == UINT64_MAX);
    simple_xray_thread_note_unattached_v1(header_a);
    REQUIRE(__atomic_load_n(&header_a->unattached_lost, __ATOMIC_RELAXED) == UINT64_MAX);

    /* Existing pins survive close; new ones fail. Drain is observable only
     * after the final exact release. */
    void *held = simple_xray_resident_acquire_v1(&g_pool_a.admission);
    REQUIRE(held == header_a);
    simple_xray_resident_close_v1(&g_pool_a.admission);
    REQUIRE(simple_xray_resident_acquire_v1(&g_pool_a.admission) == NULL);
    REQUIRE(!simple_xray_resident_drained_v1(&g_pool_a.admission));
    simple_xray_resident_release_v1(&g_pool_a.admission);
    REQUIRE(simple_xray_resident_drained_v1(&g_pool_a.admission));

    puts("PASS xray thread context and resident admission");
    return 0;
}
