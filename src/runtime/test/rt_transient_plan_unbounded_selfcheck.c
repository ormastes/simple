/* Exercise the actual runtime_native.c transient promotion and deep-free
 * planners past the removed 1<<22 node cap and verify SIZE_MAX overflow
 * refusal without triggering real extreme allocations. Unused runtime sections
 * are garbage-collected by the test linker. */
#include "../runtime_native.c"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned checks;
#define CHECK(label, cond) do { \
    ++checks; \
    if (!(cond)) { \
        fprintf(stderr, "FAIL %s (check=%u line=%d)\n", (label), checks, __LINE__); \
        return 1; \
    } \
} while (0)

int main(void) {
    const size_t old_cap = (size_t)1 << 22;
    const size_t target_nodes = old_cap + 1024;
    const size_t mid = target_nodes / 2;

    /* 1. RtCoreTransientPlan and its seen-set grow smoothly beyond 1 << 22 nodes. */
    RtCoreTransientPlan tplan;
    memset(&tplan, 0, sizeof(tplan));
    for (size_t i = 0; i < target_nodes; i++) {
        uintptr_t key = (uintptr_t)((i + 1) << 3);
        int seen_rc = rt_core_transient_seen_insert(&tplan, key);
        int pushed = rt_core_transient_plan_push(
            &tplan, (void*)(uintptr_t)(i + 1), RT_CORE_TRANSIENT_RAW, i);
        if (seen_rc != 1 || !pushed) {
            fprintf(stderr, "FAIL transient push/seen at i=%zu (seen_rc=%d pushed=%d)\n",
                    i, seen_rc, pushed);
            free(tplan.seen);
            free(tplan.nodes);
            return 1;
        }
    }
    CHECK("transient len past 1<<22", tplan.len == target_nodes);
    CHECK("transient cap past 1<<22", tplan.cap >= target_nodes);
    CHECK("transient seen_len past 1<<22", tplan.seen_len == target_nodes);
    CHECK("transient seen_cap past 1<<22", tplan.seen_cap > old_cap);
    CHECK("transient node 0 intact",
          tplan.nodes[0].ptr == (void*)(uintptr_t)1 &&
          tplan.nodes[0].kind == RT_CORE_TRANSIENT_RAW &&
          tplan.nodes[0].bytes == 0);
    CHECK("transient node mid intact",
          tplan.nodes[mid].ptr == (void*)(uintptr_t)(mid + 1) &&
          tplan.nodes[mid].bytes == mid);
    CHECK("transient node tail intact",
          tplan.nodes[target_nodes - 1].ptr == (void*)(uintptr_t)target_nodes &&
          tplan.nodes[target_nodes - 1].bytes == target_nodes - 1);
    free(tplan.seen);
    free(tplan.nodes);

    /* 2. RtCoreDeepFreePlan and its seen-set grow smoothly beyond 1 << 22 nodes. */
    RtCoreDeepFreePlan dplan;
    memset(&dplan, 0, sizeof(dplan));
    for (size_t i = 0; i < target_nodes; i++) {
        uintptr_t key = (uintptr_t)((i + 1) << 3);
        int seen_rc = rt_core_deep_free_seen_insert(&dplan, key);
        int pushed = rt_core_deep_free_plan_push(
            &dplan, (void*)(uintptr_t)(i + 1), RT_CORE_DEEP_FREE_STRING);
        if (seen_rc != 1 || !pushed) {
            fprintf(stderr, "FAIL deep_free push/seen at i=%zu (seen_rc=%d pushed=%d)\n",
                    i, seen_rc, pushed);
            free(dplan.seen);
            free(dplan.nodes);
            return 1;
        }
    }
    CHECK("deep_free len past 1<<22", dplan.len == target_nodes);
    CHECK("deep_free cap past 1<<22", dplan.cap >= target_nodes);
    CHECK("deep_free seen_len past 1<<22", dplan.seen_len == target_nodes);
    CHECK("deep_free seen_cap past 1<<22", dplan.seen_cap > old_cap);
    CHECK("deep_free node 0 intact",
          dplan.nodes[0].ptr == (void*)(uintptr_t)1 &&
          dplan.nodes[0].kind == RT_CORE_DEEP_FREE_STRING);
    CHECK("deep_free node mid intact",
          dplan.nodes[mid].ptr == (void*)(uintptr_t)(mid + 1) &&
          dplan.nodes[mid].kind == RT_CORE_DEEP_FREE_STRING);
    CHECK("deep_free node tail intact",
          dplan.nodes[target_nodes - 1].ptr == (void*)(uintptr_t)target_nodes &&
          dplan.nodes[target_nodes - 1].kind == RT_CORE_DEEP_FREE_STRING);
    free(dplan.seen);
    free(dplan.nodes);

    /* 3. Overflow guards refuse multiplication/doubling wrap before realloc/calloc. */
    RtCoreTransientPlan t_ov;
    memset(&t_ov, 0, sizeof(t_ov));
    t_ov.cap = (SIZE_MAX / 2) + 1;
    t_ov.len = t_ov.cap;
    CHECK("transient push cap*2 overflow refused",
          rt_core_transient_plan_push(&t_ov, NULL, RT_CORE_TRANSIENT_STRING, 0) == 0);
    t_ov.cap = (SIZE_MAX / sizeof(RtCoreTransientNode)) / 2 + 1;
    t_ov.len = t_ov.cap;
    CHECK("transient push sizeof overflow refused",
          rt_core_transient_plan_push(&t_ov, NULL, RT_CORE_TRANSIENT_STRING, 0) == 0);
    t_ov.seen_cap = (SIZE_MAX / 2) + 1;
    t_ov.seen_len = t_ov.seen_cap;
    CHECK("transient seen cap*2 overflow refused",
          rt_core_transient_seen_insert(&t_ov, (uintptr_t)0x1000) == -1);
    t_ov.seen_cap = (SIZE_MAX / sizeof(uintptr_t)) / 2 + 1;
    t_ov.seen_len = t_ov.seen_cap;
    CHECK("transient seen sizeof overflow refused",
          rt_core_transient_seen_insert(&t_ov, (uintptr_t)0x1000) == -1);

    RtCoreDeepFreePlan d_ov;
    memset(&d_ov, 0, sizeof(d_ov));
    d_ov.cap = (SIZE_MAX / 2) + 1;
    d_ov.len = d_ov.cap;
    CHECK("deep_free push cap*2 overflow refused",
          rt_core_deep_free_plan_push(&d_ov, NULL, RT_CORE_DEEP_FREE_STRING) == 0);
    d_ov.cap = (SIZE_MAX / sizeof(RtCoreDeepFreeNode)) / 2 + 1;
    d_ov.len = d_ov.cap;
    CHECK("deep_free push sizeof overflow refused",
          rt_core_deep_free_plan_push(&d_ov, NULL, RT_CORE_DEEP_FREE_STRING) == 0);
    d_ov.seen_cap = (SIZE_MAX / 2) + 1;
    d_ov.seen_len = d_ov.seen_cap;
    CHECK("deep_free seen grow cap*2 overflow refused",
          rt_core_deep_free_seen_grow(&d_ov) == 0);
    CHECK("deep_free seen insert overflow refused",
          rt_core_deep_free_seen_insert(&d_ov, (uintptr_t)0x1000) == -1);
    d_ov.seen_cap = (SIZE_MAX / sizeof(uintptr_t)) / 2 + 1;
    d_ov.seen_len = d_ov.seen_cap;
    CHECK("deep_free seen grow sizeof overflow refused",
          rt_core_deep_free_seen_grow(&d_ov) == 0);
    CHECK("deep_free seen insert sizeof overflow refused",
          rt_core_deep_free_seen_insert(&d_ov, (uintptr_t)0x1000) == -1);

    /* 4. Direct rt_core_seen_needs_grow boundary checks (P1 wrap & >SIZE_MAX/7 fallback). */
    CHECK("seen_needs_grow cap==0",
          rt_core_seen_needs_grow(0, 0) == 1);
    CHECK("seen_needs_grow 178/256 below 70%",
          rt_core_seen_needs_grow(178, 256) == 0);
    CHECK("seen_needs_grow 179/256 at 70%",
          rt_core_seen_needs_grow(179, 256) == 1);
    CHECK("seen_needs_grow (SIZE_MAX-1)/10 wrap boundary",
          rt_core_seen_needs_grow((SIZE_MAX - 1) / 10, SIZE_MAX / 7) == 1);
    CHECK("seen_needs_grow seen_cap > SIZE_MAX/7 fallback",
          rt_core_seen_needs_grow(SIZE_MAX - 2, SIZE_MAX - 1) == 1);

    printf("PASS rt_transient_plan_unbounded checks=%u target_nodes=%zu\n",
           checks, target_nodes);
    return 0;
}
