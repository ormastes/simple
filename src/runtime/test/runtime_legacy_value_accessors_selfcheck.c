/* Link with the real core-C legacy provider; no local symbol substitutes. */
#include "../runtime.h"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

int main(void) {
    SplValue items[3] = {0};
    const int64_t expected[3] = {INT64_MIN, INT64_C(0x123456789abcdef), INT64_MAX};
    SplArray array = {items, 3, 3};
    for (int i = 0; i < 3; ++i) {
        items[i].tag = SPL_INT;
        items[i].as_int = expected[i];
        if (spl_array_get_i64(&array, i) != expected[i]) return 10 + i;
    }
    if (spl_array_get_i64(NULL, 0) != 0) return 20;
    if (spl_array_get_i64(&array, -1) != 0) return 21;
    if (spl_array_get_i64(&array, array.len) != 0) return 22;

    /* Exercise the by-value SplValue ABI and preserve finite/negative-zero bits. */
    const double samples[3] = {42.125, -0.25, -0.0};
    for (int i = 0; i < 3; ++i) {
        SplValue value = {0};
        uint64_t expected_bits = 0, actual_bits = 0;
        value.tag = SPL_FLOAT;
        value.as_float = samples[i];
        double actual = spl_as_float(value);
        memcpy(&expected_bits, &samples[i], sizeof(expected_bits));
        memcpy(&actual_bits, &actual, sizeof(actual_bits));
        if (actual_bits != expected_bits) return 30 + i;
    }
    puts("core-c value accessors PASS");
    return 0;
}
