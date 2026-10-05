/* Pin the tagged-receiver ABI emitted by seed 817fef0 (main 1bc4bd4702b).
 * Unlike rt_to_int_dynamic's raw numeric identity, this entry decodes tags.
 * Nil retains its sentinel word, per the existing UnboxInt contract. */
#include "runtime.h"
#include <inttypes.h>
#include <stdio.h>

int main(void) {
    const int64_t values[] = {
        rt_value_int(0), rt_value_int(203), rt_value_int(-7),
        rt_value_int_wide(INT64_MAX), rt_value_int_wide(INT64_MIN),
        rt_value_bool(0), rt_value_bool(1), rt_value_nil(),
        rt_value_float(2.9), rt_value_float(-2.9), rt_value_float(0.0),
        rt_string_new((const uint8_t *)"42", 2),
        rt_string_new((const uint8_t *)"-17", 3),
        rt_string_new((const uint8_t *)"abc", 3),
        rt_string_new((const uint8_t *)"", 0)
    };
    const int64_t expected[] = {
        0, 203, -7, INT64_MAX, INT64_MIN, 0, 1, 3,
        2, -2, 0, 42, -17, 0, 0
    };
    for (size_t i = 0; i < sizeof values / sizeof values[0]; ++i) {
        int64_t actual = rt_any_to_int(values[i]);
        if (actual != expected[i]) {
            fprintf(stderr, "any-to-int case %zu: got %" PRId64
                    " expected %" PRId64 "\n", i, actual, expected[i]);
            return 1;
        }
    }
    /* Reproduce the erased collection-slot call shape, not just constructors. */
    SplArray *slots = rt_array_new(1);
    rt_array_push(slots, rt_value_int(203));
    if (rt_any_to_int(rt_array_get(slots, 0)) != 203) {
        fputs("any-to-int tagged array slot failed\n", stderr);
        return 1;
    }
    if (rt_to_int_dynamic(203) != 203 ||
        rt_to_int_dynamic(rt_value_int(203)) != 1624) {
        fputs("raw dynamic conversion contract changed\n", stderr);
        return 1;
    }
    puts("PASS: 15 tagged conversions, array slot, raw dynamic distinction");
    return 0;
}
