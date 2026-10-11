/* Link ONLY the actual Simple-owned core_values/core_string/core_memory
 * objects, their real Simple array/dict/enum/closure provider closure, and
 * selected host primitives. No C runtime_native, mocked transient API or tags.
 * Negative modes require exit1 AND exact stderr; any crash/return fails. */
#include <stdint.h>
#include <string.h>
/* runtime.h describes core-C's void hooks; selected core_values returns i64.
 * Declare the actual Simple signatures rather than calling mismatched types. */
#define __simple_runtime_init core_c_runtime_init_declaration
#define __simple_runtime_shutdown core_c_runtime_shutdown_declaration
#include "runtime.h"
#undef __simple_runtime_init
#undef __simple_runtime_shutdown

/* These are real --no-mangle Simple core_values exports, not test helpers. */
extern int64_t numeric_box_kind(int64_t value);
extern int64_t float_is_valid(int64_t value);
extern void float_reclaim_transient(int64_t pointer);
extern int64_t __simple_runtime_init(void);
extern int64_t __simple_runtime_shutdown(void);

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

    /* Persistent leaves coexist with actual Float tracking in core_memory. */
    int64_t wide_before = rt_value_int(INT64_MIN);
    int64_t uint_before = rt_value_u64(-1);
    int64_t float_before = rt_value_float(precise);
    if (rt_transient_array_scope_begin() != 1) return 13;
    if (float_is_valid(float_before) != 1) return 14;
    if (float_is_valid(wide_before) != 0 || float_is_valid(uint_before) != 0) return 15;
    int64_t float_inside_a = rt_value_float(0.5);
    int64_t wide_inside = rt_value_int(INT64_MAX);
    int64_t float_inside_b = rt_value_float(precise);
    int64_t uint_inside = rt_value_u64(INT64_MIN);
    if (float_is_valid(float_inside_a) != 1 || float_is_valid(float_inside_b) != 1) return 16;
    /* Calling the actual Float reclaimer must refuse registered Int/UInt. */
    float_reclaim_transient(wide_before & ~INT64_C(7));
    float_reclaim_transient(uint_before & ~INT64_C(7));
    float_reclaim_transient(wide_inside & ~INT64_C(7));
    float_reclaim_transient(uint_inside & ~INT64_C(7));
    if (numeric_box_kind(wide_before) != INT64_C(0x494e5431) ||
        numeric_box_kind(wide_inside) != INT64_C(0x494e5431) ||
        numeric_box_kind(uint_before) != INT64_C(0x55494e54) ||
        numeric_box_kind(uint_inside) != INT64_C(0x55494e54)) return 17;
    if (rt_transient_array_scope_end() != 1) return 18;
    /* Check membership before any allocation can reuse freed Float addresses. */
    if (float_is_valid(float_inside_a) != 0 || float_is_valid(float_inside_b) != 0) return 19;
    stored = rt_value_as_float(float_before);
    memcpy(&stored_bits, &stored, sizeof(stored_bits));
    if (float_is_valid(float_before) != 1 || stored_bits != wanted_bits) return 20;
    if (rt_value_as_int_wide(wide_before) != INT64_MIN || rt_value_as_int_wide(wide_inside) != INT64_MAX) return 21;
    if (rt_value_as_u64(uint_before) != -1 || rt_value_as_u64(uint_inside) != INT64_MIN) return 22;

    /* An early real Float reclaim followed by scope end must not free twice. */
    if (rt_transient_array_scope_begin() != 1) return 23;
    int64_t float_early = rt_value_float(precise);
    if (float_is_valid(float_early) != 1) return 24;
    float_reclaim_transient(float_early & ~INT64_C(7));
    if (float_is_valid(float_early) != 0) return 25;
    if (rt_transient_array_scope_end() != 1) return 26;
    if (float_is_valid(float_before) != 1 ||
        numeric_box_kind(wide_inside) != INT64_C(0x494e5431) ||
        numeric_box_kind(uint_inside) != INT64_C(0x55494e54)) return 27;

    /* The core_values shutdown sweep owns these persistent numeric leaves. */
    __simple_runtime_shutdown();
    if (numeric_box_kind(wide_before) != 0 || numeric_box_kind(wide_inside) != 0 ||
        numeric_box_kind(uint_before) != 0 || numeric_box_kind(uint_inside) != 0 ||
        float_is_valid(float_before) != 0) return 28;
    __simple_runtime_shutdown();
    if (numeric_box_kind(wide_before) != 0 || float_is_valid(float_before) != 0) return 29;

    /* Rebuild the actual registry after shutdown, then repeat the sweep. */
    __simple_runtime_init();
    int64_t wide_rebuilt = rt_value_int(INT64_MIN);
    int64_t uint_rebuilt = rt_value_u64(-1);
    int64_t float_rebuilt = rt_value_float(precise);
    if (numeric_box_kind(wide_rebuilt) != INT64_C(0x494e5431) ||
        numeric_box_kind(uint_rebuilt) != INT64_C(0x55494e54) ||
        float_is_valid(float_rebuilt) != 1) return 30;
    stored = rt_value_as_float(float_rebuilt);
    memcpy(&stored_bits, &stored, sizeof(stored_bits));
    if (rt_value_as_int_wide(wide_rebuilt) != INT64_MIN ||
        rt_value_as_u64(uint_rebuilt) != -1 || stored_bits != wanted_bits) return 31;
    __simple_runtime_shutdown();
    if (numeric_box_kind(wide_rebuilt) != 0 || numeric_box_kind(uint_rebuilt) != 0 ||
        float_is_valid(float_rebuilt) != 0) return 32;
    __simple_runtime_shutdown();
    if (numeric_box_kind(wide_rebuilt) != 0 || float_is_valid(float_rebuilt) != 0) return 33;
    return 0;
}
