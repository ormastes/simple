/* Element accessors on packed arrays ([u8] BYTES, [u64] U64_PACKED) hand
 * Simple code a TAGGED RuntimeValue, like their Rust twins
 * (collections.rs rt_array_get -> RuntimeValue::from_int).
 *
 * rt_array_get on a packed array returns the RAW slot. That is the C lane's
 * internal convention, and rt_array_packed_reverse_index_enumerate_selfcheck.c
 * pins it. rt_index_get, first/last/at/pop, the closure helpers
 * (map/each/reduce/filter/find/all/any), enumerate, take/drop and max used to
 * forward that raw slot. contains compared it as tagged, and reverse/sort
 * wrote it back through rt_array_set, which re-decodes it. So byte 56
 * (0b111000) came out as tagged 7. Native gzip/deflate broke because
 * lz77_compress builds `[0, data[pos], 0]` through an untyped receiver.
 * Bug: doc/08_tracking/bug/native_index_get_packed_raw_slot_2026-10-19.md
 * Link against runtime_native.c (see the header of text_sort_selfcheck.c). */
#include "runtime.h"
#include <stdio.h>
#include <string.h>

extern int64_t rt_array_first(int64_t array);
extern int64_t rt_array_at(SplArray* a, int64_t idx);
extern int64_t rt_array_pop(SplArray* a);
extern int64_t rt_array_enumerate(int64_t array);
extern int64_t rt_array_max(int64_t receiver);

static unsigned checks;
#define CHECK(x) do { ++checks; if (!(x)) { fprintf(stderr, "FAIL line=%d check=%u\n", __LINE__, checks); return 1; } } while (0)

/* A tagged (or wide-boxed) integer whose decoded value is `want`. */
static int is_value(int64_t v, int64_t want) {
    return v == rt_value_int(want) || (v != want && rt_value_unbox_int(v) == want && (v & 7) != 0);
}

static int check_packed(SplArray* arr, const int64_t* values, int n) {
    int64_t rv = (int64_t)(uintptr_t)arr;
    for (int i = 0; i < n; i++) {
        CHECK(is_value(rt_index_get(rv, rt_value_int(i)), values[i]));
        int64_t opt = rt_array_at(arr, i);
        CHECK(rt_enum_discriminant(opt) == 0 && is_value(rt_enum_payload(opt), values[i]));
        int64_t pair = rt_array_enumerate(rv);
        CHECK(is_value(rt_tuple_get(rt_index_get(pair, rt_value_int(i)), 1), values[i]));
        CHECK(rt_contains(rv, rt_value_int(values[i])));
    }
    CHECK(rt_index_get(rv, rt_value_int(n)) == rt_value_nil());
    CHECK(is_value(rt_index_get(rv, rt_value_int(-n)), values[0]));
    CHECK(is_value(rt_array_first(rv), values[0]));
    CHECK(is_value(rt_array_last(arr), values[n - 1]));
    CHECK(!rt_contains(rv, rt_value_int(9)));
    int64_t taken = rt_take(rv, 2);
    CHECK(is_value(rt_index_get(taken, rt_value_int(1)), values[1]));
    int64_t dropped = rt_drop(rv, n - 1);
    CHECK(is_value(rt_index_get(dropped, rt_value_int(0)), values[n - 1]));
    return 0;
}

int main(void) {
    /* ---- [u8] ------------------------------------------------------------ */
    const int64_t byte_values[] = {56, 0, 7, 8, 255, 64};
    SplArray* bytes = rt_byte_array_new(6);
    CHECK(bytes);
    for (int i = 0; i < 6; i++) CHECK(rt_typed_bytes_u8_push(bytes, byte_values[i]));
    if (check_packed(bytes, byte_values, 6)) return 1;
    CHECK(rt_array_get(bytes, 0) == 56); /* internal raw contract unchanged */
    CHECK(is_value(rt_array_max((int64_t)(uintptr_t)bytes), 255));

    int64_t brv = (int64_t)(uintptr_t)bytes;
    CHECK(rt_reverse_mut(brv) == brv);
    CHECK(rt_array_get(bytes, 0) == 64 && rt_array_get(bytes, 5) == 56);
    CHECK(rt_sort(brv) == brv);
    const int64_t byte_sorted[] = {0, 7, 8, 56, 64, 255};
    for (int i = 0; i < 6; i++) CHECK(rt_array_get(bytes, i) == byte_sorted[i]);
    CHECK(is_value(rt_array_pop(bytes), 255));
    CHECK(rt_array_len(bytes) == 5);

    /* ---- [u64], including words beyond the 61-bit tagged immediate ------- */
    const int64_t big = (int64_t)((1ULL << 60) + 5);
    const int64_t word_values[] = {56, 0, 7, 8, 255, big, -1 /* u64 max */};
    SplArray* words = rt_array_new_with_cap_u64(7);
    CHECK(words);
    for (int i = 0; i < 7; i++) CHECK(rt_typed_words_u64_push(words, word_values[i]));
    if (check_packed(words, word_values, 7)) return 1;
    CHECK(rt_array_get(words, 0) == 56);
    int64_t wide = rt_index_get((int64_t)(uintptr_t)words, rt_value_int(5));
    CHECK(rt_value_as_u64(wide) == big && rt_value_unbox_int(wide) == big);
    CHECK(rt_value_as_u64(rt_array_last(words)) == -1);
    {   /* to_text renders packed words unsigned, like the interpreter */
        int64_t text = rt_to_string((int64_t)(uintptr_t)words);
        const char* want = "[56, 0, 7, 8, 255, 1152921504606846981, 18446744073709551615]";
        CHECK(rt_string_len(text) == (int64_t)strlen(want));
        CHECK(memcmp(rt_string_data(text), want, strlen(want)) == 0);
    }
    CHECK(rt_sort((int64_t)(uintptr_t)words) == (int64_t)(uintptr_t)words);
    CHECK(rt_array_get(words, 0) == 0 && rt_array_get(words, 6) == -1); /* unsigned order */
    CHECK(rt_value_as_u64(rt_array_pop(words)) == -1);

    /* ---- generic arrays already hold tagged words ----------------------- */
    SplArray* generic = rt_array_new(1);
    CHECK(generic && rt_array_push(generic, rt_value_int(56)));
    CHECK(rt_index_get((int64_t)(uintptr_t)generic, rt_value_int(0)) == rt_value_int(56));
    CHECK(rt_array_first((int64_t)(uintptr_t)generic) == rt_value_int(56));

    printf("PASS rt_index_get_packed_tagged: %u checks\n", checks);
    return 0;
}
