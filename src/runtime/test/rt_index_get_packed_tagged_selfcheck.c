/* rt_index_get on packed arrays ([u8] BYTES, [u64] U64_PACKED) returns a
 * TAGGED RuntimeValue, like its Rust twin (collections.rs rt_index_get ->
 * rt_array_get -> RuntimeValue::from_int).
 *
 * rt_index_get is the ANY-boundary entry: native code calls it when the
 * receiver's static type is erased (`fn f(data): data[0]`) and stores the
 * result verbatim into untyped slots. rt_array_get on a packed array returns
 * the RAW slot (the C lane's internal convention, pinned by
 * rt_array_packed_reverse_index_enumerate_selfcheck.c), and rt_index_get used
 * to forward that raw value, so byte 56 (0b111000) later decoded as tagged 7.
 * That corrupted every literal byte that is a multiple of 8 in native
 * gzip/deflate (lz77_compress builds `[0, data[pos], 0]` through an untyped
 * receiver). Bug: doc/08_tracking/bug/native_index_get_packed_raw_slot_2026-10-19.md
 * Link against runtime_native.c (see the header of text_sort_selfcheck.c). */
#include "runtime.h"
#include <stdio.h>

static unsigned checks;
#define CHECK(x) do { ++checks; if (!(x)) { fprintf(stderr, "FAIL line=%d check=%u\n", __LINE__, checks); return 1; } } while (0)

int main(void) {
    SplArray* bytes = rt_byte_array_new(4);
    CHECK(bytes);
    const int64_t byte_values[] = {56, 7, 0, 255};
    for (int i = 0; i < 4; i++) CHECK(rt_typed_bytes_u8_push(bytes, byte_values[i]));
    int64_t bytes_rv = (int64_t)(uintptr_t)bytes;
    for (int i = 0; i < 4; i++) {
        CHECK(rt_index_get(bytes_rv, rt_value_int(i)) == rt_value_int(byte_values[i]));
    }
    CHECK(rt_index_get(bytes_rv, rt_value_int(-4)) == rt_value_int(56));
    CHECK(rt_index_get(bytes_rv, rt_value_int(4)) == rt_value_nil());
    /* the internal raw-slot contract of rt_array_get is unchanged */
    CHECK(rt_array_get(bytes, 0) == 56);

    SplArray* words = rt_array_new_with_cap_u64(3);
    CHECK(words);
    const int64_t word_values[] = {56, 1, 40};
    for (int i = 0; i < 3; i++) CHECK(rt_typed_words_u64_push(words, word_values[i]));
    int64_t words_rv = (int64_t)(uintptr_t)words;
    for (int i = 0; i < 3; i++) {
        CHECK(rt_index_get(words_rv, rt_value_int(i)) == rt_value_int(word_values[i]));
    }
    CHECK(rt_array_get(words, 0) == 56);

    /* generic arrays already hold tagged words and pass through untouched */
    SplArray* generic = rt_array_new(1);
    CHECK(generic && rt_array_push(generic, rt_value_int(56)));
    CHECK(rt_index_get((int64_t)(uintptr_t)generic, rt_value_int(0)) == rt_value_int(56));

    printf("PASS rt_index_get_packed_tagged: %u checks\n", checks);
    return 0;
}
