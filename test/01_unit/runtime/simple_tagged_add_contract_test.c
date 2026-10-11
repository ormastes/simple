/* Link ONLY the actual Simple-owned core_values/core_string runtime objects
 * plus their selected host primitives. No C runtime_native or mocked tags.
 * Negative modes require exit1 AND exact stderr; any crash/return fails. */
#include <stdint.h>
#include <string.h>
#include "runtime.h"

static int text_equal(int64_t value, const char* expected) {
    size_t length = strlen(expected);
    return rt_string_len(value) == (int64_t)length &&
        memcmp(rt_string_data(value), expected, length) == 0;
}

int main(int argc, char** argv) {
    if (argc > 1) {
        if (strcmp(argv[1], "text-float") == 0) {
            (void)rt_tagged_add(rt_string_new((const uint8_t*)"n=", 2), rt_value_float(2.5));
            return 31;
        }
        if (strcmp(argv[1], "text-unregistered") == 0) {
            (void)rt_tagged_add(rt_string_new((const uint8_t*)"n=", 2), INT64_C(4096) | 1);
            return 31;
        }
        int64_t operand;
        if (strcmp(argv[1], "nil") == 0) operand = rt_value_nil();
        else if (strcmp(argv[1], "uint") == 0) operand = rt_value_u64(-1);
        else if (strcmp(argv[1], "unregistered") == 0) operand = INT64_C(4096) | 1;
        else return 30;
        (void)rt_tagged_add(operand, rt_value_int(1));
        return 31;
    }
    if (rt_value_as_int_wide(rt_tagged_add(rt_value_int(5), rt_value_int(3))) != 8) return 1;
    if (rt_value_as_float(rt_tagged_add(rt_value_float(2.5), rt_value_float(0.5))) != 3.0) return 2;
    if (rt_value_as_float(rt_tagged_add(rt_value_int(3), rt_value_float(2.5))) != 5.5) return 3;
    if (rt_value_as_int_wide(rt_tagged_add(rt_value_int(INT64_MAX), rt_value_int(1))) != INT64_MIN) return 4;
    if (rt_value_as_int_wide(rt_tagged_add(rt_value_int(INT64_MIN), rt_value_int(-1))) != INT64_MAX) return 5;
    if (rt_value_as_int_wide(rt_tagged_add(rt_value_int(INT64_C(1152921504606846975)), rt_value_int(1))) != INT64_C(1152921504606846976)) return 6;
    int64_t prefix = rt_string_new((const uint8_t*)"n=", 2);
    if (!text_equal(rt_tagged_add(prefix, rt_value_int(INT64_MIN)), "n=-9223372036854775808")) return 7;
    if (!text_equal(rt_tagged_add(prefix, rt_value_u64(-1)), "n=18446744073709551615")) return 8;
    if (!text_equal(rt_tagged_add(prefix, rt_value_nil()), "n=")) return 9;
    if (rt_any_add(rt_value_int(5), rt_value_int(3)) != rt_value_int(8)) return 10;
    if (!text_equal(rt_tagged_add(prefix, rt_value_int(INT64_C(1152921504606846976))), "n=1152921504606846976")) return 11;
    uint64_t wanted_bits = UINT64_C(0x3ff0000000000001), stored_bits;
    double precise, stored;
    memcpy(&precise, &wanted_bits, sizeof(precise));
    stored = rt_value_as_float(rt_tagged_add(rt_value_float(precise), rt_value_float(0.0)));
    memcpy(&stored_bits, &stored, sizeof(stored_bits));
    if (stored_bits != wanted_bits) return 12;
    return 0;
}
