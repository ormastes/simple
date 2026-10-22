/* Packed-array and wide-integer hardening for the core-C runtime, one block
 * per defect (all pre-existing, found while fixing native gzip):
 *
 *   1. rt_string_join / rt_array_join_any read every element as an 8-byte
 *      slot, so a [u8] (BYTES) array was read past its buffer, and integer
 *      elements rendered as "" (Rust renders them with rt_value_to_string).
 *   2. rt_index_set / rt_push stored a TAGGED value verbatim into a
 *      U64_PACKED array (56 became 448); the read side hands out raw words.
 *   4. rt_native_eq had no heap wide-int arm, the dict hashed wide boxes by
 *      pointer, and rt_sort_cmp ranked wide boxes Equal (so max/sort of
 *      words >= 2^60 was wrong).
 *
 * Every expected value is pinned numerically against the raw slot contents
 * (byte for byte, word for word), so a byte-order dependent read or write
 * would fail here on a big-endian host too.
 * Bug: doc/08_tracking/bug/runtime_array_hardening_2026-10-19.md
 * Build: cc -std=gnu11 -ffunction-sections -fdata-sections -I src/runtime \
 *   src/runtime/test/rt_array_hardening_selfcheck.c src/runtime/runtime_native.c \
 *   -Wl,--gc-sections -lm -pthread -ldl */
#include "runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int64_t rt_array_join_any(int64_t array, int64_t separator);
extern int64_t rt_array_max(int64_t receiver);

/* runtime.c owns spl_panic; this selfcheck links runtime_native.c alone. */
void spl_panic(const char* msg) {
    fprintf(stderr, "panic: %s\n", msg);
    abort();
}

static unsigned checks;
#define CHECK(x) do { ++checks; if (!(x)) { fprintf(stderr, "FAIL line=%d check=%u\n", __LINE__, checks); return 1; } } while (0)

static int text_is(int64_t s, const char* want) {
    size_t n = strlen(want);
    return rt_string_len(s) == (int64_t)n && (n == 0 || memcmp(rt_string_data(s), want, n) == 0);
}

static int64_t rv(SplArray* a) { return (int64_t)(uintptr_t)a; }

int main(void) {
    const int64_t big = (int64_t)((1ULL << 60) + 5);
    const int64_t bigger = (int64_t)(1ULL << 61);
    int64_t comma = rt_string_new((const uint8_t*)",", 1);

    /* ---- 1. join over packed layouts and integer elements ---------------- */
    SplArray* bytes = rt_byte_array_new(3);
    CHECK(bytes);
    for (int i = 0; i < 3; i++) CHECK(rt_typed_bytes_u8_push(bytes, 65 + i));
    CHECK(text_is(rt_string_join(rv(bytes), comma), "65,66,67"));
    CHECK(text_is(rt_array_join_any(rv(bytes), comma), "65,66,67"));
    SplArray* words = rt_array_new_with_cap_u64(2);
    CHECK(words);
    CHECK(rt_typed_words_u64_push(words, 65));
    CHECK(rt_typed_words_u64_push(words, big));
    CHECK(text_is(rt_string_join(rv(words), comma), "65,1152921504606846981"));
    CHECK(text_is(rt_array_join_any(rv(words), comma), "65,1152921504606846981"));
    SplArray* ints = rt_array_new(3);
    CHECK(rt_array_push(ints, rt_value_int(1)));
    CHECK(rt_array_push(ints, rt_string_new((const uint8_t*)"x", 1)));
    CHECK(rt_array_push(ints, rt_value_int(10000)));
    CHECK(text_is(rt_string_join(rv(ints), comma), "1,x,10000"));

    /* ---- 2. RuntimeValue writes into packed arrays store the raw element --
     * rt_index_set / rt_push are the entry points compiled code hands a
     * RuntimeValue (`data[i] = v`, `data.push(v)` on an untyped receiver). */
    SplArray* w = rt_array_new_with_cap_u64(4);
    CHECK(w);
    CHECK(rt_typed_words_u64_push(w, 1));
    CHECK(rt_typed_words_u64_push(w, 2));
    CHECK(rt_index_set(rv(w), rt_value_int(0), rt_value_int(56)));
    CHECK(rt_push(rv(w), rt_value_int(9)) == rv(w));
    CHECK(rt_push(rv(w), rt_value_int(big)) == rv(w));          /* wide box */
    CHECK(rt_push(rv(w), rt_value_u64((int64_t)-1)) == rv(w));  /* u64 box */
    CHECK(rt_index_set(rv(w), rt_value_int(-4), rt_value_int(8)));
    const uint64_t want_words[] = {56, 8, 9, (uint64_t)big, UINT64_MAX};
    CHECK(rt_array_len(w) == 5);
    for (int i = 0; i < 5; i++) CHECK(rt_typed_words_u64_at(w, i) == (int64_t)want_words[i]);
    /* rt_array_set / rt_array_push keep the C lane's raw-word contract */
    CHECK(rt_array_set(w, 0, 40) && rt_typed_words_u64_at(w, 0) == 40);
    CHECK(rt_index_set(rv(bytes), rt_value_int(0), rt_value_int(56)));
    CHECK(rt_push(rv(bytes), rt_value_u64(200)) == rv(bytes));
    CHECK(rt_array_len(bytes) == 4);
    const uint8_t want_bytes[] = {56, 66, 67, 200};
    for (int i = 0; i < 4; i++) CHECK(rt_bytes_u8_at(bytes, i) == want_bytes[i]);

    /* ---- 4. wide integers compare, hash and order by value --------------- */
    int64_t a = rt_value_int(big), b = rt_value_int(big);
    CHECK(a != b);                               /* two distinct boxes */
    CHECK(rt_native_eq(a, b) == 1);
    CHECK(rt_native_eq(a, rt_value_int(bigger)) == 0);
    CHECK(rt_native_eq(a, rt_value_u64(big)) == 1);   /* u64 box, same value */
    CHECK(rt_native_eq(rt_value_u64(big), a) == 1);
    CHECK(rt_native_eq(rt_value_int(-big), rt_value_u64(-big)) == 0);
    CHECK(rt_native_eq(a, rt_value_int(5)) == 0);
    int64_t d = rt_dict_new(4);
    CHECK(rt_dict_set(d, a, rt_value_int(1)));
    CHECK(rt_dict_contains(d, b));
    CHECK(rt_dict_get(d, b) == rt_value_int(1));
    CHECK(rt_dict_contains(d, rt_value_u64(big)));
    CHECK(!rt_dict_contains(d, rt_value_int(bigger)));

    SplArray* g = rt_array_new(4);          /* generic array of tagged/wide */
    CHECK(rt_array_push(g, rt_value_int(bigger)));
    CHECK(rt_array_push(g, rt_value_int(5)));
    CHECK(rt_array_push(g, a));
    CHECK(rt_array_push(g, rt_value_int(-bigger)));
    CHECK(rt_native_eq(rt_array_max(rv(g)), rt_value_int(bigger)));
    CHECK(rt_sort(rv(g)) == rv(g));
    const int64_t sorted_g[] = {-bigger, 5, big, bigger};
    for (int i = 0; i < 4; i++) CHECK(rt_native_eq(rt_array_get(g, i), rt_value_int(sorted_g[i])));

    SplArray* p = rt_array_new_with_cap_u64(3);   /* packed [u64] max */
    CHECK(rt_typed_words_u64_push(p, big));
    CHECK(rt_typed_words_u64_push(p, bigger));
    CHECK(rt_typed_words_u64_push(p, 5));
    CHECK(rt_native_eq(rt_array_max(rv(p)), rt_value_int(bigger)));
    CHECK(rt_typed_words_u64_push(p, (int64_t)-1));     /* u64::MAX is the max */
    CHECK(rt_value_as_u64(rt_array_max(rv(p))) == (int64_t)-1);

    printf("PASS rt_array_hardening: %u checks\n", checks);
    return 0;
}
