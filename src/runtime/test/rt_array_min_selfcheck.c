/* C-lane twin of the Rust rt_array_min (runtime/src/value/collections.rs).
 * The C runtime had rt_array_max but no rt_array_min, so native-build of any
 * program calling `[T].min()` failed to link ("rt_array_min has no
 * definition"). Pins: nil for an empty array and a non-array, tagged ints,
 * floats, wide (heap-boxed) ints, and packed [u8] / [u64] arrays compared as
 * raw UNSIGNED elements (a word >= 2^63 is not the minimum).
 * Bug: doc/08_tracking/bug/compiled_float_array_sum_reads_boxed_float_as_int_2026-11-24.md
 * Build: clang -std=gnu11 -ffunction-sections -fdata-sections -I src/runtime \
 *   src/runtime/test/rt_array_min_selfcheck.c src/runtime/runtime_native.c \
 *   -fuse-ld=lld -Wl,--gc-sections -lm -pthread -ldl */
#include "runtime.h"
#include <stdio.h>
#include <stdlib.h>

extern int64_t rt_array_min(int64_t receiver);
extern int64_t rt_array_max(int64_t receiver);

#ifndef SIMPLE_TEST_CORE_RUNTIME
void spl_panic(const char* msg) {
    fprintf(stderr, "panic: %s\n", msg);
    abort();
}
#endif

static unsigned checks;
#define CHECK(x) do { ++checks; if (!(x)) { fprintf(stderr, "FAIL line=%d check=%u\n", __LINE__, checks); return 1; } } while (0)

static int64_t rv(SplArray* a) { return (int64_t)(uintptr_t)a; }

int main(void) {
    const int64_t bigger = (int64_t)(1ULL << 61);

    CHECK(rt_array_min(rv(rt_array_new(0))) == rt_value_nil());
    CHECK(rt_array_min(rt_value_int(5)) == rt_value_nil());

    SplArray* ints = rt_array_new(4);
    CHECK(rt_array_push(ints, rt_value_int(7)));
    CHECK(rt_array_push(ints, rt_value_int(-3)));
    CHECK(rt_array_push(ints, rt_value_int(bigger)));
    CHECK(rt_array_push(ints, rt_value_int(-bigger)));
    CHECK(rt_native_eq(rt_array_min(rv(ints)), rt_value_int(-bigger)));
    CHECK(rt_native_eq(rt_array_max(rv(ints)), rt_value_int(bigger)));

    SplArray* floats = rt_array_new(3);
    CHECK(rt_array_push(floats, rt_value_float(2.5)));
    CHECK(rt_array_push(floats, rt_value_float(-1.25)));
    CHECK(rt_array_push(floats, rt_value_float(9.0)));
    CHECK(rt_value_as_float(rt_array_min(rv(floats))) == -1.25);

    SplArray* bytes = rt_byte_array_new(4);
    const int64_t byte_values[] = {56, 255, 7, 64};
    for (int i = 0; i < 4; i++) CHECK(rt_typed_bytes_u8_push(bytes, byte_values[i]));
    CHECK(rt_native_eq(rt_array_min(rv(bytes)), rt_value_int(7)));

    SplArray* words = rt_array_new_with_cap_u64(3);
    CHECK(rt_typed_words_u64_push(words, (int64_t)-1));          /* u64::MAX */
    CHECK(rt_typed_words_u64_push(words, (int64_t)(1ULL << 63)));
    CHECK(rt_typed_words_u64_push(words, 5));
    CHECK(rt_native_eq(rt_array_min(rv(words)), rt_value_int(5)));
    SplArray* high = rt_array_new_with_cap_u64(2);
    CHECK(rt_typed_words_u64_push(high, (int64_t)-1));
    CHECK(rt_typed_words_u64_push(high, (int64_t)(1ULL << 63)));
    CHECK(rt_value_as_u64(rt_array_min(rv(high))) == (int64_t)(1ULL << 63));

    printf("PASS rt_array_min: %u checks\n", checks);
    return 0;
}
