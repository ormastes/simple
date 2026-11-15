/* Probe: are runtime tuple (and array) dict keys found by VALUE?
 *
 * A runtime tuple is an RtCoreArray flagged RT_CORE_ARRAY_FLAG_TUPLE
 * (rt_tuple_new is rt_array_new). rt_core_dict_key_eq already compares two
 * registered arrays STRUCTURALLY (rt_native_eq -> rt_core_array_eq), but
 * rt_core_dict_hash hashed every non-string/int/float key by ADDRESS, so two
 * equal tuples built separately landed in different buckets and the equality
 * that would have matched them never ran: d[(1, 2)] missed.
 *
 * The hash must agree with that equality for every pair it calls equal:
 * nested tuples, text compared by content, float elements compared by IEEE
 * `==` (so -0.0 == +0.0), wide integer boxes compared by value, enums compared
 * by id/discriminant/payload. A tuple and an array holding the same elements
 * are equal to rt_core_array_eq (the TUPLE flag is not compared), so they are
 * ONE dict key.
 *
 * P0 is the live control (int keys). T* are the tuple rows. A1 is the array
 * side effect. H1 reports (does not assert) the mutated-array-key hazard.
 *
 * Build + run (clang, never gcc; never -lsqlite3 -- unresolved externs of
 * unrelated hosted providers are left unresolved, this probe never calls them):
 *   clang -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/dict_tuple_probe \
 *     src/runtime/test/rt_dict_tuple_key_hash_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE 'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time|counterpart_worker|slang_ggml|sosix_darwin') \
 *     -Wl,--unresolved-symbols=ignore-all -lm -lpthread -ldl
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

extern int64_t rt_tuple_new(int64_t len);
extern int8_t  rt_tuple_set(int64_t tuple, int64_t idx, int64_t value);
extern int64_t rt_tuple_get(int64_t tuple, int64_t idx);
extern void*   rt_array_new(int64_t cap);
extern int8_t  rt_array_push(void* a, int64_t val);
extern int64_t rt_array_len_safe(int64_t value);
extern int64_t rt_array_get(void* a, int64_t idx);
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_value_float(double value_f64);
extern int64_t rt_value_int_wide(int64_t value);
extern int64_t rt_enum_new(int32_t enum_id, int32_t discriminant, int64_t payload);
extern int64_t rt_dict_new(int64_t cap_hint);
extern int8_t  rt_dict_set(int64_t dict, int64_t key, int64_t value);
extern int64_t rt_dict_get(int64_t dict, int64_t key);
extern int8_t  rt_dict_contains(int64_t dict, int64_t key);
extern int8_t  rt_dict_remove(int64_t dict, int64_t key);
extern int64_t rt_dict_len(int64_t dict);
extern int64_t rt_dict_keys(int64_t dict);
extern int64_t rt_native_eq(int64_t left, int64_t right);

static int failures = 0;

static int64_t mki(int64_t v) { return v << 3; }

static int64_t text(const char* s) { return rt_string_new((const uint8_t*)s, strlen(s)); }

static int64_t tup2(int64_t a, int64_t b) {
    int64_t t = rt_tuple_new(2);
    rt_tuple_set(t, 0, a);
    rt_tuple_set(t, 1, b);
    return t;
}

static int64_t arr2(int64_t a, int64_t b) {
    void* x = rt_array_new(2);
    rt_array_push(x, a);
    rt_array_push(x, b);
    return (int64_t)(uintptr_t)x;
}

static void check(const char* row, int ok) {
    printf("%s %s\n", ok ? "PASS" : "FAIL", row);
    if (!ok) failures++;
}

/* A fresh dict holding `key -> 1`, probed with a separately built `probe`. */
static int hits(int64_t key, int64_t probe) {
    int64_t d = rt_dict_new(0);
    rt_dict_set(d, key, mki(1));
    return rt_native_eq(key, probe) && rt_dict_get(d, probe) == mki(1) && rt_dict_contains(d, probe);
}

int main(void) {
    {   /* P0: int keys, the shared path every other key kind relies on. */
        int64_t d = rt_dict_new(0);
        rt_dict_set(d, mki(4), mki(40));
        check("P0 int key control", rt_dict_get(d, mki(4)) == mki(40) && rt_dict_len(d) == 1);
    }
    check("T1 (1, 2) built twice hits", hits(tup2(mki(1), mki(2)), tup2(mki(1), mki(2))));
    {   /* T2: distinct tuples do not collide into one entry. */
        int64_t d = rt_dict_new(0);
        rt_dict_set(d, tup2(mki(1), mki(2)), mki(12));
        rt_dict_set(d, tup2(mki(2), mki(1)), mki(21));
        rt_dict_set(d, tup2(mki(1), mki(3)), mki(13));
        check("T2 distinct tuples stay distinct",
              rt_dict_len(d) == 3 &&
              rt_dict_get(d, tup2(mki(2), mki(1))) == mki(21) &&
              rt_dict_get(d, tup2(mki(1), mki(3))) == mki(13) &&
              rt_dict_get(d, tup2(mki(1), mki(2))) == mki(12));
        /* T3: an equal key overwrites in place. */
        rt_dict_set(d, tup2(mki(1), mki(2)), mki(99));
        check("T3 equal tuple overwrites", rt_dict_len(d) == 3 && rt_dict_get(d, tup2(mki(1), mki(2))) == mki(99));
        /* T4: removal by an equal, separately built key. */
        rt_dict_remove(d, tup2(mki(2), mki(1)));
        check("T4 remove by equal tuple", rt_dict_len(d) == 2 && !rt_dict_contains(d, tup2(mki(2), mki(1))));
        /* T10: keys() hands back tuple objects with the stored elements. */
        int64_t keys = rt_dict_keys(d);
        int ok = rt_array_len_safe(keys) == 2;
        for (int64_t i = 0; ok && i < 2; i++) {
            int64_t k = rt_array_get((void*)(uintptr_t)keys, i);
            ok = rt_tuple_get(k, 0) == mki(1) && (rt_tuple_get(k, 1) == mki(2) || rt_tuple_get(k, 1) == mki(3));
        }
        check("T10 keys() round-trips tuple elements", ok);
    }
    check("T5 (text, i64) with separate text boxes", hits(tup2(text("ab"), mki(7)), tup2(text("ab"), mki(7))));
    check("T5n different text content misses", !hits(tup2(text("ab"), mki(7)), tup2(text("ac"), mki(7))));
    check("T6 nested ((1, 2), 3)", hits(tup2(tup2(mki(1), mki(2)), mki(3)), tup2(tup2(mki(1), mki(2)), mki(3))));
    check("T7 float element boxed twice", hits(tup2(rt_value_float(1.5), mki(0)), tup2(rt_value_float(1.5), mki(0))));
    check("T7z -0.0 element equals +0.0 element", hits(tup2(rt_value_float(-0.0), mki(0)), tup2(rt_value_float(0.0), mki(0))));
    check("T8 wide int element boxed twice",
          hits(tup2(rt_value_int_wide((int64_t)1 << 62), mki(0)), tup2(rt_value_int_wide((int64_t)1 << 62), mki(0))));
    check("T9 enum element built twice",
          hits(tup2(rt_enum_new(7, 2, mki(5)), mki(0)), tup2(rt_enum_new(7, 2, mki(5)), mki(0))));
    check("T9n enum payload differs misses",
          !hits(tup2(rt_enum_new(7, 2, mki(5)), mki(0)), tup2(rt_enum_new(7, 2, mki(6)), mki(0))));
    /* A1: side effect. Arrays share the tuple representation and equality,
     * so an array key is now found by value, and [1, 2] and (1, 2) are one key. */
    check("A1 array [1, 2] built twice hits", hits(arr2(mki(1), mki(2)), arr2(mki(1), mki(2))));
    check("A1t array [1, 2] and tuple (1, 2) are one key", hits(tup2(mki(1), mki(2)), arr2(mki(1), mki(2))));
    {   /* H1 (reported, not asserted): mutating an array after using it as a
         * key changes its hash; the entry stays in the old bucket. */
        int64_t d = rt_dict_new(0);
        int64_t a = arr2(mki(1), mki(2));
        rt_dict_set(d, a, mki(1));
        rt_array_push((void*)(uintptr_t)a, mki(3));
        printf("INFO H1 mutated array key: len=%lld same-object-hit=%d fresh-[1,2]-hit=%d\n",
               (long long)rt_dict_len(d), (int)rt_dict_contains(d, a),
               (int)rt_dict_contains(d, arr2(mki(1), mki(2))));
    }
    printf("%s: %d failure(s)\n", failures ? "FAIL" : "PASS", failures);
    return failures ? 1 : 0;
}
