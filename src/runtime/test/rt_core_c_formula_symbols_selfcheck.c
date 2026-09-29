#include "runtime.h"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int failures = 0;
#define CHECK(expr) do { if (!(expr)) { \
    fprintf(stderr, "FAIL line %d: %s\n", __LINE__, #expr); failures++; \
} } while (0)

int main(void) {
    CHECK(rt_math_fma(1.0 + 0x1p-27, 1.0 - 0x1p-27, -1.0) == -0x1p-54);
    double negative_zero = -0.0;
    int64_t bits = 0;
    memcpy(&bits, &negative_zero, sizeof(bits));
    CHECK(rt_f64_to_bits(negative_zero) == bits);

    SplArray* floats = rt_f64_array_alloc(3);
    SplArray* singles = rt_f32_array_alloc(2);
    SplArray* integers = rt_i64_array_alloc(2);
    CHECK(floats != NULL && rt_array_len(floats) == 3);
    CHECK(singles != NULL && rt_array_len(singles) == 2);
    CHECK(integers != NULL && rt_array_len(integers) == 2);
    if (floats) {
        for (int64_t i = 0; i < 3; i++) {
            int64_t item = rt_array_get(floats, i);
            CHECK(rt_value_is_float(item) && rt_value_as_float(item) == 0.0);
        }
    }
    if (singles) {
        for (int64_t i = 0; i < 2; i++) {
            int64_t item = rt_array_get(singles, i);
            CHECK(rt_value_is_float(item) && rt_value_as_float(item) == 0.0);
        }
    }
    if (integers) {
        for (int64_t i = 0; i < 2; i++) CHECK(rt_array_get(integers, i) == rt_value_int(0));
    }

    SplArray* mixed = rt_array_new(3);
    CHECK(mixed != NULL);
    if (mixed) {
        CHECK(rt_array_push(mixed, rt_value_int(2)));
        CHECK(rt_array_push(mixed, rt_value_float(0.5)));
        CHECK(rt_array_push(mixed, rt_value_int(-1)));
        int64_t sum = rt_numeric_sum_f64((int64_t)(uintptr_t)mixed);
        CHECK(rt_value_is_float(sum) && rt_value_as_float(sum) == 1.5);
        CHECK(rt_array_push(mixed, rt_string_new((const uint8_t*)"x", 1)));
        CHECK(rt_numeric_sum_f64((int64_t)(uintptr_t)mixed) == 3);
    }
    CHECK(rt_numeric_sum_f64(3) == 3);
    SplArray* empty = rt_f64_array_alloc(-3);
    CHECK(empty != NULL && rt_array_len(empty) == 0);

    int64_t random_empty = rt_random_bytes_c(0);
    CHECK(rt_array_len((SplArray*)(uintptr_t)random_empty) == 0);
    int64_t random_bytes = rt_random_bytes_c(32);
    CHECK(rt_array_len((SplArray*)(uintptr_t)random_bytes) == 32);
    CHECK(rt_array_is_byte_packed((SplArray*)(uintptr_t)random_bytes));
    uint8_t sampled[32] = {0};
    CHECK(rt_array_bytes_copy_checked(random_bytes, sampled, 32) == 32);
    int has_entropy = 0;
    for (int i = 0; i < 32; i++) has_entropy |= sampled[i] != 0;
    CHECK(has_entropy);
    double unit = rt_random_random();
    double next_unit = rt_random_random();
    CHECK(unit >= 0.0 && unit < 1.0);
    CHECK(next_unit >= 0.0 && next_unit < 1.0 && next_unit != unit);

    int64_t haystack = rt_string_new((const uint8_t*)"abcabc", 6);
    int64_t needle = rt_string_new((const uint8_t*)"bc", 2);
    int64_t missing = rt_string_new((const uint8_t*)"zz", 2);
    CHECK(rt_simd_str_search(haystack, needle) == 1);
    CHECK(rt_simd_str_search(haystack, missing) == -1);

    if (failures) return 1;
    puts("PASS rt_core_c_formula_symbols_selfcheck");
    return 0;
}
