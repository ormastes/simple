/* Self-check for rt_dict_free_deep / rt_free_deep -- the dict half of the
 * refuse-biased, all-or-nothing deep-free family.
 *
 * rt_dict_free_deep shares rt_array_free_deep's planner, so the cases that
 * matter are the ones the dict shape adds on top of the array contract:
 *   - case 3: an INTERNED string used as a KEY must refuse the whole call. A
 *     naive implementation classifies values but trusts keys, which would free
 *     a literal out from under the process-wide intern table.
 *   - case 5: tombstoned/emptied slots retain stale key/value words from a
 *     previous occupant. Walking `cap` slots without checking occupied==1 would
 *     follow those words and free memory the dict no longer owns -- a
 *     use-after-free that only shows up after a remove.
 *   - case 6: cross-KIND aliasing. The same string reachable both as a dict key
 *     and as an element of an array stored as a dict value must refuse. This is
 *     the case a "call rt_array_free_deep, then rt_dict_free_deep" chain gets
 *     WRONG: two planners each see a clean tree and between them double-free.
 *   - case 8: rt_free_deep must dispatch on the ROOT kind and must refuse a
 *     root it cannot identify.
 *
 * Negative control (documented so a future reader can re-run it): in
 * runtime_native.c, change the dict walk's `if (e->occupied != 1) continue;` to
 * `if (e->occupied == 0) continue;` -- case 5 then fails. Change the dict
 * branch to skip classifying `e->key` (only classify `e->value`) -- case 3 and
 * case 6 then fail. Delete the `RT_VALUE_HEAP_DICT` arm of
 * rt_core_deep_free_classify -- cases 4, 7 and 9 then fail. Measured results
 * for all three are recorded in
 * doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md
 *
 * Build + run (the runtime dir holds mutually-exclusive alternative TUs):
 *   gcc -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/rtdf \
 *     src/runtime/test/rt_dict_free_deep_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time') \
 *     -lm -lpthread -ldl -lsqlite3 && /tmp/rtdf
 */
#include <stdio.h>
#include <string.h>
#include <stdint.h>

typedef struct SplArray SplArray;

extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_new_literal(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_len(int64_t value);
extern int64_t rt_string_free(int64_t value);
extern int64_t rt_heap_registry_count(void);

extern SplArray* rt_array_new(int64_t cap);
extern int8_t rt_array_push(SplArray* array, int64_t value);
extern int64_t rt_array_len(SplArray* array);
extern int64_t rt_array_get(SplArray* array, int64_t idx);
extern int64_t rt_array_free_deep(int64_t value);

extern int64_t rt_dict_new(int64_t cap_hint);
extern int8_t rt_dict_set(int64_t dict, int64_t key, int64_t value);
extern int64_t rt_dict_get(int64_t dict, int64_t key);
extern int8_t rt_dict_remove(int64_t dict, int64_t key);
extern int8_t rt_dict_contains(int64_t dict, int64_t key);
extern int64_t rt_dict_len(int64_t dict);
extern int64_t rt_dict_free_deep(int64_t value);
extern int64_t rt_free_deep(int64_t value);

extern int64_t rt_enum_new(int32_t enum_id, int32_t discriminant, int64_t payload);

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

static int64_t handle(SplArray* a) { return (int64_t)(uintptr_t)a; }

/* Tagged small int, matching rt_value_int's representation for leaf slots. */
static int64_t tagged_int(int64_t v) { return (v << 3) | 2; }

int main(void) {
    char buf[96];

    /* ---- 1. root validation: only a registered dict is a valid root ---- */
    printf("case 1: root validation\n");
    check(rt_dict_free_deep(0) == 0, "nil root refuses");
    check(rt_dict_free_deep(7) == 0, "small tag-aliasing int refuses");
    check(rt_dict_free_deep(tagged_int(123456)) == 0, "tagged int root refuses");
    {
        SplArray* arr = rt_array_new(4);
        check(rt_dict_free_deep(handle(arr)) == 0, "an ARRAY root refuses (wrong primitive)");
        check(rt_array_len(arr) == 0, "the refused array is still readable");
        check(rt_array_free_deep(handle(arr)) == 1, "and still freeable by its own primitive");
    }
    {
        const char* text = "a string root belongs to rt_string_free";
        int64_t s = mkstr(text);
        check(rt_dict_free_deep(s) == 0, "a STRING root refuses");
        check(rt_string_len(s) == (int64_t)strlen(text), "the refused string is intact");
        check(rt_string_free(s) == 1, "and still freeable");
    }

    /* ---- 2. the happy path: string keys, string values ---- */
    printf("case 2: flat string->string dict\n");
    {
        int64_t base = rt_heap_registry_count();
        int64_t d = rt_dict_new(0);
        for (int i = 0; i < 32; i++) {
            snprintf(buf, sizeof buf, "deep-free-dict-key-%d", i);
            int64_t k = mkstr(buf);
            snprintf(buf, sizeof buf, "deep-free-dict-value-%d", i);
            int64_t v = mkstr(buf);
            rt_dict_set(d, k, v);
        }
        check(rt_dict_len(d) == 32, "32 entries stored");
        int64_t peak = rt_heap_registry_count();
        check(peak == base + 1 + 64, "registry grew by dict + 32 keys + 32 values");
        check(rt_dict_free_deep(d) == 1, "flat dict deep-freed");
        check(rt_heap_registry_count() == base,
              "registry dropped by exactly 65 -- keys AND values reclaimed");
        check(rt_dict_free_deep(d) == 0, "second free of the same dict refuses");
    }

    /* ---- 3. an interned KEY must refuse the whole call ---- */
    printf("case 3: interned key refuses (keys are classified like values)\n");
    {
        int64_t base = rt_heap_registry_count();
        int64_t d = rt_dict_new(0);
        int64_t lit = rt_string_new_literal(
            (const uint8_t*)"interned-literal-key", 20);
        int64_t plain_k = mkstr("plain-key-alongside-the-literal");
        int64_t plain_v = mkstr("plain-value-alongside-the-literal");
        rt_dict_set(d, lit, mkstr("value-under-the-interned-key"));
        rt_dict_set(d, plain_k, plain_v);
        int64_t peak = rt_heap_registry_count();
        check(rt_dict_free_deep(d) == 0, "dict with an interned KEY refuses");
        check(rt_heap_registry_count() == peak,
              "refusal freed NOTHING -- registry unchanged");
        check(rt_dict_len(d) == 2, "the refused dict is still readable");
        check(rt_string_len(lit) == 20, "the interned key is intact");
        check(rt_dict_contains(d, plain_k) == 1, "the innocent entry survived too");
        /* clean up by hand: remove the interned key, then the dict frees */
        rt_dict_remove(d, lit);
        check(rt_dict_free_deep(d) == 1, "after removing the interned key it frees");
        (void)base;
    }

    /* ---- 4. nested: dict -> dict -> array -> string ---- */
    printf("case 4: heterogeneous nest\n");
    {
        int64_t base = rt_heap_registry_count();
        int64_t outer = rt_dict_new(0);
        for (int i = 0; i < 8; i++) {
            int64_t inner = rt_dict_new(0);
            SplArray* leaves = rt_array_new(4);
            for (int j = 0; j < 4; j++) {
                snprintf(buf, sizeof buf, "nest-%d-%d", i, j);
                rt_array_push(leaves, mkstr(buf));
            }
            snprintf(buf, sizeof buf, "inner-key-%d", i);
            rt_dict_set(inner, mkstr(buf), handle(leaves));
            snprintf(buf, sizeof buf, "outer-key-%d", i);
            rt_dict_set(outer, mkstr(buf), inner);
        }
        /* per i: inner dict + inner key + array + 4 leaves + outer key = 8 */
        int64_t peak = rt_heap_registry_count();
        check(peak == base + 1 + 8 * 8, "registry grew by 1 + 8*8");
        check(rt_dict_free_deep(outer) == 1, "3-level heterogeneous nest deep-freed");
        check(rt_heap_registry_count() == base, "every node reclaimed, nothing stranded");
    }

    /* ---- 5. tombstoned slots must NOT be followed ---- */
    printf("case 5: removed entries leave stale words that must be skipped\n");
    {
        int64_t base = rt_heap_registry_count();
        int64_t d = rt_dict_new(0);
        int64_t doomed_k = mkstr("removed-key-whose-slot-keeps-stale-words");
        int64_t doomed_v = mkstr("removed-value-whose-slot-keeps-stale-words");
        rt_dict_set(d, doomed_k, doomed_v);
        for (int i = 0; i < 6; i++) {
            snprintf(buf, sizeof buf, "survivor-key-%d", i);
            rt_dict_set(d, mkstr(buf), mkstr("survivor-value"));
        }
        check(rt_dict_remove(d, doomed_k) == 1, "one entry removed (leaves a tombstone)");
        /* The removed pair is still ours: free it explicitly, so if the walk
         * followed the tombstone it would be freeing already-freed memory and
         * the registry accounting below would not add up. */
        check(rt_string_free(doomed_k) == 1, "removed key freed by hand");
        check(rt_string_free(doomed_v) == 1, "removed value freed by hand");
        check(rt_dict_free_deep(d) == 1, "dict with a tombstone deep-freed");
        check(rt_heap_registry_count() == base,
              "exactly the live entries were reclaimed, tombstone not followed");
    }

    /* ---- 6. cross-kind aliasing refuses ---- */
    printf("case 6: an alias that crosses array/dict boundaries refuses\n");
    {
        int64_t base = rt_heap_registry_count();
        int64_t d = rt_dict_new(0);
        const char* shared_text = "this-string-is-both-a-key-and-an-array-element";
        int64_t shared = mkstr(shared_text);
        SplArray* arr = rt_array_new(4);
        rt_array_push(arr, shared);
        rt_dict_set(d, shared, handle(arr));
        int64_t peak = rt_heap_registry_count();
        check(peak == base + 3, "dict + string + array registered");
        check(rt_dict_free_deep(d) == 0, "cross-kind alias refuses the whole call");
        check(rt_heap_registry_count() == peak, "refusal freed NOTHING");
        check(rt_string_len(shared) == (int64_t)strlen(shared_text),
              "the aliased string is intact");
        check(rt_array_get((SplArray*)(uintptr_t)rt_dict_get(d, shared), 0) == shared,
              "the dict and the array are both still traversable");
        /* dismantle by hand */
        rt_dict_remove(d, shared);
        check(rt_dict_free_deep(d) == 1, "emptied dict frees");
        check(rt_array_free_deep(handle(arr)) == 1, "array (owning the string) frees");
        check(rt_heap_registry_count() == base, "hand dismantle reclaimed everything");
    }

    /* ---- 6b. self-reference (cycle) refuses ---- */
    printf("case 6b: a dict holding itself refuses\n");
    {
        int64_t base = rt_heap_registry_count();
        int64_t d = rt_dict_new(0);
        rt_dict_set(d, mkstr("self"), d);
        int64_t peak = rt_heap_registry_count();
        check(rt_dict_free_deep(d) == 0, "self-referencing dict refuses");
        check(rt_heap_registry_count() == peak, "refusal freed NOTHING");
        check(rt_dict_len(d) == 1, "still readable after refusal");
        (void)base;
    }

    /* ---- 7. an unfreeable VALUE kind refuses ---- */
    printf("case 7: a value with no free path refuses\n");
    {
        int64_t d = rt_dict_new(0);
        rt_dict_set(d, mkstr("enum-value-key"), rt_enum_new(1, 0, tagged_int(9)));
        rt_dict_set(d, mkstr("ordinary-key"), mkstr("ordinary-value"));
        int64_t peak = rt_heap_registry_count();
        check(rt_dict_free_deep(d) == 0, "dict holding an enum refuses");
        check(rt_heap_registry_count() == peak, "refusal freed NOTHING");
        check(rt_dict_len(d) == 2, "still readable after refusal");
    }

    /* ---- 8. rt_free_deep dispatches on the root kind ---- */
    printf("case 8: rt_free_deep dispatch\n");
    {
        int64_t base = rt_heap_registry_count();
        int64_t d = rt_dict_new(0);
        rt_dict_set(d, mkstr("dispatch-key"), mkstr("dispatch-value"));
        check(rt_free_deep(d) == 1, "dict root dispatches to rt_dict_free_deep");

        SplArray* arr = rt_array_new(4);
        rt_array_push(arr, mkstr("dispatch-array-element"));
        check(rt_free_deep(handle(arr)) == 1, "array root dispatches to rt_array_free_deep");

        int64_t s = mkstr("dispatch-string");
        check(rt_free_deep(s) == 1, "string root dispatches to rt_string_free");

        int64_t lit = rt_string_new_literal((const uint8_t*)"interned-root", 13);
        check(rt_free_deep(lit) == 0, "interned string root refuses");

        check(rt_free_deep(0) == 0, "nil refuses");
        check(rt_free_deep(tagged_int(4096)) == 0, "tagged int refuses");
        check(rt_free_deep(rt_enum_new(2, 1, tagged_int(3))) == 0, "enum root refuses");
        check(rt_heap_registry_count() == base + 2,
              "only the enum and the interned literal remain from this case");
    }

    /* ---- 9. probe-chain integrity over the shared registry ---- */
    printf("case 9: batch free, then prove survivors intact and still freeable\n");
    {
        enum { N = 200 };
        int64_t base = rt_heap_registry_count();
        int64_t roots[N];
        for (int i = 0; i < N; i++) {
            roots[i] = rt_dict_new(0);
            snprintf(buf, sizeof buf, "probe-chain-dict-key-%d", i);
            rt_dict_set(roots[i], mkstr(buf), mkstr("probe-chain-dict-value"));
        }
        int64_t peak = rt_heap_registry_count();
        check(peak == base + 3 * N, "each dict registered 3 objects");

        int freed = 0;
        for (int i = 0; i < N; i += 2) {
            if (rt_dict_free_deep(roots[i]) == 1) freed++;
        }
        check(freed == N / 2, "every even-indexed dict deep-freed");
        check(rt_heap_registry_count() == peak - 3 * freed,
              "registry dropped by exactly 3 per freed dict");

        int survivors_ok = 1;
        for (int i = 1; i < N; i += 2) {
            snprintf(buf, sizeof buf, "probe-chain-dict-key-%d", i);
            if (rt_dict_len(roots[i]) != 1) { survivors_ok = 0; break; }
        }
        check(survivors_ok, "all survivors still readable");

        int refreed = 0;
        for (int i = 1; i < N; i += 2) {
            if (rt_dict_free_deep(roots[i]) == 1) refreed++;
        }
        check(refreed == N / 2, "every survivor still registered and freed");
        check(rt_heap_registry_count() == base, "whole batch reclaimed, nothing stranded");
    }

    /* ---- 10. tables still work after the churn ---- */
    printf("case 10: post-churn\n");
    {
        int64_t d = rt_dict_new(0);
        rt_dict_set(d, mkstr("post-churn-key"), mkstr("post-churn-value"));
        check(rt_dict_free_deep(d) == 1, "post-churn dict frees");
    }

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
