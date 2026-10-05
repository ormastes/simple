/* Exercise the public compiler-condition ABI against real core-C values. */
#include "runtime.h"
#include <math.h>
#include <stdio.h>

int main(void) {
    const int64_t values[] = {
        rt_value_nil(), rt_value_bool(0), rt_value_bool(1),
        rt_value_int(0), rt_value_int(1), rt_value_int(-1),
        rt_value_float(0.0), rt_value_float(-0.0),
        rt_value_float(1.25), rt_value_float(NAN),
        rt_value_u64(0), rt_value_u64(1), rt_value_u64(-1),
        rt_value_int_wide(INT64_MAX),
        rt_string_new((const uint8_t *)"", 0),
        rt_string_new((const uint8_t *)"x", 1),
        1 /* tagged null heap pointer */
    };
    const int8_t expected[] = {0, 0, 1, 0, 1, 1, 0, 0, 1, 1,
                               0, 1, 1, 1, 1, 1, 0};
    for (size_t i = 0; i < sizeof values / sizeof values[0]; ++i) {
        int8_t actual = rt_value_truthy(values[i]);
        if (actual != expected[i]) {
            fprintf(stderr, "truthy case %zu: got %d expected %d\n",
                    i, actual, expected[i]);
            return 1;
        }
    }
    puts("PASS: 17 core-C truthiness cases");
    return 0;
}
