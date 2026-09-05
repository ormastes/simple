/* Self-check for rt_string_free + the tombstoned immortal registry.
 *
 * The registry is open-addressed and, until rt_string_free existed, had NO
 * deletion. Erasing by writing 0 would truncate any probe chain running
 * through that slot, so unrelated LIVE strings would silently start reading as
 * unregistered. Case 5 is the one that catches that: it frees every other
 * string out of a large batch and then re-checks that all survivors are still
 * usable. It fails loudly on a naive (tombstone-less) erase.
 *
 * Build + run:
 *   cc -std=gnu11 -O1 -o /tmp/rtsf src/runtime/test/rt_string_free_selfcheck.c \
 *      src/runtime/runtime_native.c -lm -lpthread && /tmp/rtsf
 */
#include <stdio.h>
#include <string.h>
#include <stdint.h>

extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_new_literal(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_free(int64_t value);
extern int64_t rt_heap_registry_count(void);
extern int64_t rt_heap_live_bytes(void);
extern int64_t rt_heap_peak_bytes(void);
extern int64_t rt_string_len(int64_t value);
extern int64_t rt_string_concat(int64_t left, int64_t right);
extern int64_t rt_push(int64_t receiver, int64_t value);
extern void spl_memtrack_record(void* ptr, int64_t size, const char* tag);
extern void spl_memtrack_unrecord(void* ptr);

static int failures = 0;

static void check(int cond, const char* what) {
    if (cond) {
        printf("  ok   %s\n", what);
    } else {
        printf("  FAIL %s\n", what);
        failures++;
    }
}

static int64_t mkstr(const char* s) {
    return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s));
}

int main(void) {
    /* Core-C durable snapshot counters use the allocation tracker owner. */
    int tracked_probe = 0;
    int64_t live_before = rt_heap_live_bytes();
    int64_t peak_before = rt_heap_peak_bytes();
    spl_memtrack_record(&tracked_probe, 17, "selfcheck");
    check(rt_heap_live_bytes() == live_before + 17, "tracked live bytes increase exactly");
    check(rt_heap_peak_bytes() >= peak_before && rt_heap_peak_bytes() >= live_before + 17,
          "tracked peak bytes retain high water");
    spl_memtrack_unrecord(&tracked_probe);
    check(rt_heap_live_bytes() == live_before, "tracked live bytes return to baseline");

    int64_t push_left = mkstr("core push ");
    int64_t push_right = mkstr("provider");
    int64_t pushed_text = rt_push(push_left, push_right);
    int64_t expected_text = rt_string_concat(push_left, push_right);
    check(pushed_text != 3 && rt_string_len(pushed_text) == rt_string_len(expected_text),
          "receiver-dispatched text push returns concatenated text");

    /* 1. an ordinary heap string is reclaimed, and the registry shrinks */
    int64_t before = rt_heap_registry_count();
    int64_t a = mkstr("a reasonably long unique string for case one");
    check(rt_heap_registry_count() == before + 1, "new string registers (+1)");
    check(rt_string_free(a) == 1, "ordinary string is freed");
    check(rt_heap_registry_count() == before, "registry count returns to baseline");

    /* 2. double free is refused, not a crash or a second decrement */
    int64_t after_first = rt_heap_registry_count();
    check(rt_string_free(a) == 0, "double free refused");
    check(rt_heap_registry_count() == after_first, "refused free does not decrement");

    /* 3. process-wide short-string cache entries are refused.
     *    len<=1 goes through rt_core_short_string_cache and is shared by every
     *    caller, so freeing one would corrupt all the others. */
    int64_t sh = mkstr("x");
    check(rt_string_free(sh) == 0, "short/cached string refused");
    int64_t sh2 = mkstr("x");
    check(rt_string_len(sh2) == 1, "short string still usable after refused free");

    /* 4. interned literals are refused (same object per literal site) */
    static const uint8_t lit[] = "an interned literal value";
    int64_t l1 = rt_string_new_literal(lit, sizeof(lit) - 1);
    check(rt_string_free(l1) == 0, "interned literal refused");
    int64_t l2 = rt_string_new_literal(lit, sizeof(lit) - 1);
    check(l1 == l2, "literal interning still returns the same object");
    check(rt_string_len(l2) == (int64_t)(sizeof(lit) - 1), "interned literal intact");

    /* 5. PROBE-CHAIN INTEGRITY -- the case a tombstone-less erase fails.
     *    Allocate many strings (forcing collisions and growth), free every
     *    other one, then confirm every survivor is still registered and
     *    readable. Freeing must not strand entries later in a probe chain. */
    enum { N = 4096 };
    static int64_t v[N];
    char buf[64];
    for (int i = 0; i < N; i++) {
        snprintf(buf, sizeof buf, "probe-chain-integrity-string-%d", i);
        v[i] = mkstr(buf);
    }
    int64_t peak = rt_heap_registry_count();
    int freed = 0;
    for (int i = 0; i < N; i += 2) {
        if (rt_string_free(v[i]) == 1) freed++;
    }
    check(freed == N / 2, "every even-indexed string freed");
    check(rt_heap_registry_count() == peak - freed, "registry dropped by exactly the freed count");

    int survivors_ok = 1;
    for (int i = 1; i < N; i += 2) {
        snprintf(buf, sizeof buf, "probe-chain-integrity-string-%d", i);
        if (rt_string_len(v[i]) != (int64_t)strlen(buf)) { survivors_ok = 0; break; }
    }
    check(survivors_ok, "all survivors still readable after interleaved frees");

    /* survivors must still be freeable -- proves they were never stranded */
    int refreed = 0;
    for (int i = 1; i < N; i += 2) {
        if (rt_string_free(v[i]) == 1) refreed++;
    }
    check(refreed == N / 2, "every survivor still found in the registry and freed");

    /* 6. reuse after heavy churn: the table must still accept inserts */
    int64_t r = mkstr("post-churn allocation must still register and free");
    check(r != 0, "allocation works after churn");
    check(rt_string_free(r) == 1, "post-churn string frees");

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
