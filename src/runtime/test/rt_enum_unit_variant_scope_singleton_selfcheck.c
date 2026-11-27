/* Payload-less enum variants survive the transient scope they were built in.
 *
 * Bug option_struct_none_box_freed_by_transient_scope_2026_11_09 (general
 * class behind stage3_native_build_heap_corruption_c0000374_2026_11_08):
 * `Option<struct>`'s native `nil` is the heap-boxed None from
 * rt_option_none(). Built inside a transient scope it used to be a
 * scope-owned box, freed at rt_transient_array_scope_end, so a function that
 * returned it past scope end handed its caller a dangling pointer. Payload-
 * less variants now intern as process-lifetime singletons regardless of the
 * active scope. The core-C bootstrap runtime capsule compiles and runs this.
 */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>

#include "../runtime.h"


#define TAGGED_NIL 0x3LL
#define TAGGED_TRUE 0xBLL
#define CUSTOM_ENUM_ID 77
#define CUSTOM_UNIT_DISC 2
#define CUSTOM_PAYLOAD_DISC 3

static int failures = 0;

/* Stress keys live in a private enum-id range so earlier checks and the
 * interned non-unit path never pre-populate them. */
#define STRESS_THREADS 4
#define STRESS_KEYS 64
#define STRESS_ITERATIONS 2000
#define STRESS_ENUM_ID_BASE 9000

typedef struct StressResult {
    int seed;
    int stable;
    int64_t none;
    int64_t seen[STRESS_KEYS];
} StressResult;

static void* stress_worker(void* arg) {
    StressResult* r = (StressResult*)arg;
    r->stable = 1;
    for (int k = 0; k < STRESS_KEYS; k++) r->seen[k] = 0;
    for (int i = 0; i < STRESS_ITERATIONS; i++) {
        /* Each thread walks the key set in a different order so publishes
         * collide on different keys at the same moment. */
        int k = (i * (2 * r->seed + 1) + r->seed) % STRESS_KEYS; /* odd stride: covers every key */
        int64_t v = rt_enum_new(STRESS_ENUM_ID_BASE + (k / 4), (int32_t)(k % 4), (k & 1) ? TAGGED_NIL : 0);
        if (r->seen[k] == 0) r->seen[k] = v;
        else if (r->seen[k] != v) r->stable = 0;
        r->none = rt_option_none();
    }
    return NULL;
}

static void check(int condition, const char* message) {
    if (condition) {
        printf("  ok   %s\n", message);
    } else {
        printf("  FAIL %s\n", message);
        failures++;
    }
}

int main(void) {
    int64_t outside_none = rt_option_none();
    int64_t outside_unit = rt_enum_new(CUSTOM_ENUM_ID, CUSTOM_UNIT_DISC, 0);
    check(rt_is_none(outside_none) == 1, "None built outside any scope is none");

    check(rt_transient_array_scope_begin() == 1, "scope begins");
    int64_t scoped_none = rt_option_none();
    int64_t scoped_unit = rt_enum_new(CUSTOM_ENUM_ID, CUSTOM_UNIT_DISC, 0);
    int64_t scoped_unit_nil_payload = rt_enum_new(CUSTOM_ENUM_ID, CUSTOM_UNIT_DISC, TAGGED_NIL);
    int64_t scoped_payload = rt_enum_new(CUSTOM_ENUM_ID, CUSTOM_PAYLOAD_DISC, rt_string_new((const uint8_t*)"owned", 5));
    int64_t scoped_ok_true = rt_enum_new(CUSTOM_ENUM_ID, CUSTOM_PAYLOAD_DISC, TAGGED_TRUE);
    int64_t scoped_int_payload = rt_enum_new(CUSTOM_ENUM_ID, CUSTOM_PAYLOAD_DISC, 5 << 3);
    check(scoped_none == outside_none, "None built inside a scope is the same singleton as outside");
    check(scoped_ok_true == rt_enum_new(CUSTOM_ENUM_ID, CUSTOM_PAYLOAD_DISC, TAGGED_TRUE),
          "bool payload variant built inside a scope is a singleton");
    check(scoped_unit == outside_unit, "unit variant (payload 0) built inside a scope is the outside singleton");
    check(scoped_unit_nil_payload != scoped_unit,
          "unit variant with nil payload interns separately from payload 0");
    check(rt_transient_array_scope_pause() == 1, "scope pauses");
    check(rt_transient_heap_promote(scoped_none) == 1, "promoting the None singleton is a no-op success");
    check(rt_transient_array_scope_end() == 1, "scope ends");

    /* The scope is gone; every payload-less box must still be live and
     * answer through the registry-checked readers. */
    check(rt_is_none(scoped_none) == 1, "None still reads as none after scope end");
    check(rt_enum_discriminant(scoped_unit) == CUSTOM_UNIT_DISC,
          "unit variant still answers its discriminant after scope end");
    check(rt_enum_id(scoped_unit) == CUSTOM_ENUM_ID, "unit variant still answers its enum id after scope end");
    check(rt_enum_discriminant(scoped_unit_nil_payload) == CUSTOM_UNIT_DISC,
          "nil-payload unit variant still answers after scope end");
    /* Control: an unpromoted heap-payload variant IS scope-owned and is
     * reclaimed (the registry no longer knows it). */
    check(rt_enum_discriminant(scoped_payload) == -1,
          "heap-payload variant left in the scope is reclaimed at scope end");
    check(rt_enum_discriminant(scoped_ok_true) == CUSTOM_PAYLOAD_DISC,
          "bool-payload variant still answers after scope end");
    check(rt_enum_discriminant(scoped_int_payload) == -1,
          "non-unit scalar payload variant keeps scoped-box behaviour (reclaimed)");

    /* A later scope reuses the singletons rather than boxing again. */
    check(rt_transient_array_scope_begin() == 1, "second scope begins");
    check(rt_option_none() == outside_none, "second scope reuses the None singleton");
    int64_t scoped_some = rt_option_some(rt_string_new((const uint8_t*)"payload", 7));
    check(scoped_some != outside_none && rt_is_none(scoped_some) == 0,
          "Some with a heap payload is still a fresh box");
    check(rt_transient_array_scope_pause() == 1, "second scope pauses");
    check(rt_transient_array_scope_end() == 1, "second scope ends");
    check(rt_is_none(outside_none) == 1, "None singleton survives a second scope");

    /* Concurrency: the singleton list is published lock-free. Threads race
     * on the same fresh key set; every thread must observe one pointer per
     * key, identical across threads (no duplicate singleton ever escapes). */
    pthread_t workers[STRESS_THREADS];
    StressResult results[STRESS_THREADS];
    int spawn_ok = 1;
    for (int t = 0; t < STRESS_THREADS; t++) {
        results[t].seed = t;
        if (pthread_create(&workers[t], NULL, stress_worker, &results[t]) != 0) spawn_ok = 0;
    }
    check(spawn_ok, "stress threads spawned");
    for (int t = 0; t < STRESS_THREADS; t++) pthread_join(workers[t], NULL);
    int consistent = 1;
    for (int t = 0; t < STRESS_THREADS; t++) {
        if (!results[t].stable) consistent = 0;
        for (int k = 0; k < STRESS_KEYS; k++) {
            if (results[t].seen[k] == 0 || results[t].seen[k] != results[0].seen[k]) consistent = 0;
        }
    }
    check(consistent, "racing threads agree on one singleton per key, stable across iterations");
    int distinct_ok = 1;
    for (int a = 0; a < STRESS_KEYS && distinct_ok; a++) {
        for (int b = a + 1; b < STRESS_KEYS; b++) {
            if (results[0].seen[a] == results[0].seen[b]) { distinct_ok = 0; break; }
        }
    }
    check(distinct_ok, "distinct keys map to distinct singletons under contention");
    int none_shared = 1;
    for (int t = 0; t < STRESS_THREADS; t++) {
        if (results[t].none != outside_none) none_shared = 0;
    }
    check(none_shared, "Option.None singleton is identical on every thread");

    if (failures == 0) {
        printf("SELFCHECK PASSED (0 failures)\n");
        return 0;
    }
    printf("SELFCHECK FAILED (%d failures)\n", failures);
    return 1;
}
