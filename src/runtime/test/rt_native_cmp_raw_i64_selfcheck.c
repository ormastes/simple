/* Raw native comparisons must not interpret integer low bits as float tags. */
#include "runtime.h"
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

int main(void) {
    const int64_t words[] = {
        INT64_MIN, INT64_MIN + 2, -99, -98, -17, -16, -15, -14, -13, -12,
        -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1,
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
        72, 97, 98, 99, INT64_MAX - 1, INT64_MAX
    };
    size_t count = sizeof words / sizeof words[0];
    for (size_t i = 0; i < count; ++i) {
        for (size_t j = 0; j < count; ++j) {
            int64_t expected = (words[i] > words[j]) - (words[i] < words[j]);
            int64_t actual = rt_native_cmp(words[i], words[j]);
            if (actual != expected) {
                fprintf(stderr, "cmp(%" PRId64 ",%" PRId64 ")=%" PRId64
                        " expected %" PRId64 "\n", words[i], words[j], actual, expected);
                return 1;
            }
        }
    }
    int64_t a = rt_string_new((const uint8_t*)"alpha", 5);
    int64_t same = rt_string_new((const uint8_t*)"alpha", 5);
    int64_t b = rt_string_new((const uint8_t*)"beta", 4);
    assert(rt_native_cmp(a, b) < 0);
    assert(rt_native_cmp(b, a) > 0);
    assert(rt_native_cmp(a, same) == 0);

    int64_t low = rt_value_float(-1.5), high = rt_value_float(2.5);
    assert((low & 7) == 1 && (high & 7) == 1);
    assert(rt_native_cmp(low, high) < 0);
    assert(rt_native_cmp(high, low) > 0);
    assert(rt_native_cmp(high, rt_value_float(2.5)) == 0);
    assert(rt_native_cmp(high, 2) > 0);
    assert(rt_native_cmp(2, high) < 0);
    assert(rt_native_cmp(rt_value_float(-0.0), rt_value_float(0.0)) == 0);

    /* Typed legacy float decoding remains available, including the OOM
     * representation; only the untyped raw-word comparison stops guessing. */
    double value = 2.5;
    int64_t legacy;
    memcpy(&legacy, &value, sizeof legacy);
    legacy = (legacy & ~INT64_C(7)) | 2;
    assert(rt_value_is_float(legacy));
    assert(rt_value_as_float(legacy) == 2.5);
    assert(rt_native_cmp(legacy, 0) == 1);
    printf("PASS: %zu raw comparisons, heap text/float ordering, legacy typed decode\n", count * count);
    return 0;
}
