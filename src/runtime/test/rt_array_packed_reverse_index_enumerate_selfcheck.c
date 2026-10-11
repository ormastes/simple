/* rt_reverse / rt_array_index_of on packed ([u8] BYTES, [u64] U64_PACKED)
 * arrays, and the rt_array_enumerate tuple shape.
 *
 * Packed arrays store RAW slots; a generic array stores tagged words. Before
 * this check existed:
 *   - rt_reverse rebuilt the result with get+push into a GENERIC array, so a
 *     reversed byte array held raw bytes that every consumer read as tagged;
 *   - rt_array_index_of compared a raw slot against a tagged needle with
 *     rt_native_eq and never matched;
 *   - rt_array_enumerate built 2-element ARRAYS holding a RAW index, unlike
 *     the Rust runtime's (tagged index, element) tuples.
 * Link against runtime_native.c (see the header of text_sort_selfcheck.c). */
#include "runtime.h"
#include <stdio.h>
#include <string.h>

extern int64_t rt_array_index_of(SplArray* array, int64_t value);
extern int64_t rt_array_enumerate(int64_t array);

static unsigned checks;
#define CHECK(x) do { ++checks; if (!(x)) { fprintf(stderr, "FAIL line=%d check=%u\n", __LINE__, checks); return 1; } } while (0)

int main(void) {
    /* ---- [u8]: raw 1-byte slots ---------------------------------------- */
    SplArray* bytes = rt_byte_array_new(4);
    CHECK(bytes);
    const int64_t byte_values[] = {7, 200, 0, 3};
    for (int i = 0; i < 4; i++) CHECK(rt_array_push(bytes, rt_value_int(byte_values[i])));
    CHECK(rt_array_len(bytes) == 4);
    CHECK(rt_array_get(bytes, 1) == 200); /* raw, not tagged */

    SplArray* rbytes = (SplArray*)(uintptr_t)rt_reverse((int64_t)(uintptr_t)bytes);
    CHECK(rbytes && rbytes != bytes && rt_array_len(rbytes) == 4);
    for (int i = 0; i < 4; i++) CHECK(rt_array_get(rbytes, i) == byte_values[3 - i]);
    /* the input is untouched and the copy keeps the byte layout */
    for (int i = 0; i < 4; i++) CHECK(rt_array_get(bytes, i) == byte_values[i]);
    CHECK(rt_array_push(rbytes, rt_value_int(0x1ff)));
    CHECK(rt_array_get(rbytes, 4) == 0xff);

    CHECK(rt_array_index_of(bytes, rt_value_int(7)) == 0);
    CHECK(rt_array_index_of(bytes, rt_value_int(200)) == 1);
    CHECK(rt_array_index_of(bytes, rt_value_int(0)) == 2);
    CHECK(rt_array_index_of(bytes, rt_value_int(3)) == 3);
    CHECK(rt_array_index_of(bytes, rt_value_int(9)) == -1);
    CHECK(rt_array_index_of(bytes, rt_value_int(-1)) == -1);
    CHECK(rt_array_index_of(bytes, rt_value_nil()) == -1);

    SplArray* empty_bytes = rt_byte_array_new(0);
    SplArray* rempty = (SplArray*)(uintptr_t)rt_reverse((int64_t)(uintptr_t)empty_bytes);
    CHECK(rempty && rt_array_len(rempty) == 0);
    CHECK(rt_array_index_of(empty_bytes, rt_value_int(0)) == -1);

    /* ---- [u64]: raw 8-byte slots --------------------------------------- */
    SplArray* words = rt_array_new_with_cap_u64(3);
    CHECK(words);
    const uint64_t word_values[] = {5, 0xffffffffffffffffULL, 40};
    for (int i = 0; i < 3; i++) CHECK(rt_array_push(words, (int64_t)word_values[i]));
    SplArray* rwords = (SplArray*)(uintptr_t)rt_reverse((int64_t)(uintptr_t)words);
    CHECK(rwords && rwords != words && rt_array_len(rwords) == 3);
    for (int i = 0; i < 3; i++) CHECK((uint64_t)rt_array_get(rwords, i) == word_values[2 - i]);
    CHECK(rt_array_index_of(words, rt_value_int(5)) == 0);
    CHECK(rt_array_index_of(words, rt_value_int(40)) == 2);
    CHECK(rt_array_index_of(words, rt_value_int(41)) == -1);

    /* ---- generic tagged array: unchanged behaviour --------------------- */
    SplArray* ints = rt_array_new(3);
    CHECK(ints);
    const int64_t int_values[] = {3, -1, 2};
    for (int i = 0; i < 3; i++) CHECK(rt_array_push(ints, rt_value_int(int_values[i])));
    SplArray* rints = (SplArray*)(uintptr_t)rt_reverse((int64_t)(uintptr_t)ints);
    CHECK(rints && rints != ints && rt_array_len(rints) == 3);
    for (int i = 0; i < 3; i++) CHECK(rt_array_get(rints, i) == rt_value_int(int_values[2 - i]));
    for (int i = 0; i < 3; i++) CHECK(rt_array_get(ints, i) == rt_value_int(int_values[i]));
    CHECK(rt_array_index_of(ints, rt_value_int(-1)) == 1);
    CHECK(rt_array_index_of(ints, rt_value_int(9)) == -1);

    /* ---- enumerate: (tagged index, element) TUPLES --------------------- */
    SplArray* pairs = (SplArray*)(uintptr_t)rt_array_enumerate((int64_t)(uintptr_t)ints);
    CHECK(pairs && rt_array_len(pairs) == 3);
    for (int i = 0; i < 3; i++) {
        int64_t pair = rt_array_get(pairs, i);
        CHECK(rt_tuple_get(pair, 0) == rt_value_int(i));
        CHECK(rt_tuple_get(pair, 1) == rt_value_int(int_values[i]));
    }
    SplArray* no_ints = rt_array_new(0);
    SplArray* no_pairs = (SplArray*)(uintptr_t)rt_array_enumerate((int64_t)(uintptr_t)no_ints);
    CHECK(no_pairs && rt_array_len(no_pairs) == 0);
    CHECK(rt_array_enumerate(rt_value_int(4)) == rt_value_nil());

    /* ---- Rust-parity math: round is half AWAY from zero ---------------- */
    CHECK(rt_math_round(2.5) == 3.0);
    CHECK(rt_math_round(-2.5) == -3.0);
    CHECK(rt_math_round(0.4) == 0.0);
    CHECK(rt_math_abs(-2.5) == 2.5);
    CHECK(rt_math_abs(2.5) == 2.5);

    printf("PASS rt_array_packed_reverse_index_enumerate checks=%u bytes=1 u64=1 generic=1 enumerate_tuples=1 math=1\n", checks);
    return 0;
}
