/* Link ONLY the actual Simple-owned core_values/core_string/core_memory/core_array_query
 * objects, their real Simple array/dict/enum/closure provider closure, and
 * selected host primitives. No C runtime_native, mocked transient API or tags.
 * Negative modes require exit1 AND exact stderr; any crash/return fails. */
#include <stdint.h>
#include <string.h>
/* runtime.h describes core-C's void hooks; selected core_values returns i64.
 * Declare the actual Simple signatures rather than calling mismatched types. */
#define __simple_runtime_init core_c_runtime_init_declaration
#define __simple_runtime_shutdown core_c_runtime_shutdown_declaration
#define rt_array_new core_c_array_new_declaration
#define rt_array_len core_c_array_len_declaration
#define rt_array_get core_c_array_get_declaration
#define rt_array_push core_c_array_push_declaration
#define rt_array_free core_c_array_free_declaration
#include "runtime.h"
#undef __simple_runtime_init
#undef __simple_runtime_shutdown
#undef rt_array_new
#undef rt_array_len
#undef rt_array_get
#undef rt_array_push
#undef rt_array_free

/* These are real --no-mangle Simple core_values exports, not test helpers. */
extern int64_t numeric_box_kind(int64_t value);
extern int64_t float_is_valid(int64_t value);
extern void float_reclaim_transient(int64_t pointer);
extern int64_t __simple_runtime_init(void);
extern int64_t __simple_runtime_shutdown(void);
extern int64_t rt_array_new(int64_t capacity);
extern int64_t rt_array_len(int64_t array);
extern int64_t rt_array_get(int64_t array, int64_t index);
extern int8_t rt_array_push(int64_t array, int64_t value);
extern void rt_array_free(int64_t array);
extern int64_t rt_array_sum(int64_t array);
extern int64_t rt_array_min(int64_t array);
extern int64_t rt_array_max(int64_t array);
extern int64_t rt_array_index_of(int64_t array, int64_t value);
extern int64_t rt_array_last_index_of(int64_t array, int64_t value);
extern int64_t rt_array_count(int64_t array, int64_t value);
extern int64_t rt_array_unique(int64_t array);
extern int8_t rt_array_sort(int64_t array);
extern int64_t rt_array_all_truthy(int64_t array);

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
    /* Ordinary conversion must consume default rt_value_int's wide boxes,
     * independently of rt_tagged_add's specialized text coercion path. */
    __simple_runtime_init();
    int64_t text_min = rt_value_int(INT64_MIN);
    int64_t text_max = rt_value_int(INT64_MAX);
    int64_t text_boundary = rt_value_int(INT64_C(1152921504606846976));
    int64_t text_uint = rt_value_u64(-1);
    if (!text_equal(rt_to_string(text_min), "-9223372036854775808")) return 34;
    if (!text_equal(rt_to_string(text_max), "9223372036854775807")) return 35;
    if (!text_equal(rt_to_string(text_boundary), "1152921504606846976")) return 36;
    if (!text_equal(rt_value_to_string(text_min), "-9223372036854775808")) return 37;
    if (!text_equal(rt_value_to_string(text_max), "9223372036854775807")) return 38;
    if (!text_equal(rt_value_to_string(text_boundary), "1152921504606846976")) return 39;
    if (!text_equal(rt_to_string(text_uint), "18446744073709551615")) return 40;
    if (!text_equal(rt_value_to_string(text_uint), "18446744073709551615")) return 41;
    if (!text_equal(rt_to_string(rt_value_bool(1)), "true") ||
        !text_equal(rt_value_to_string(rt_value_bool(0)), "false")) return 42;
    if (!text_equal(rt_to_string(rt_value_nil()), "") ||
        !text_equal(rt_value_to_string(rt_value_nil()), "")) return 43;
    int64_t text_owned = rt_string_new((const uint8_t*)"ok", 2);
    if (rt_to_string(text_owned) != text_owned || rt_value_to_string(text_owned) != text_owned) return 44;
    /* Unknown heap-tag candidates must reach the existing empty fallback
     * without a speculative header read or access violation. */
    if (!text_equal(rt_to_string(INT64_C(4096) | 1), "") ||
        !text_equal(rt_value_to_string(INT64_C(4096) | 1), "")) return 45;
    /* Ordinary Simple legacy Add must consume the new default INT1 boxes. */
    if (rt_value_as_int_wide(rt_any_add(text_max, rt_value_int(1))) != INT64_MIN) return 46;
    if (rt_value_as_int_wide(rt_any_add(text_min, rt_value_int(-1))) != INT64_MAX) return 47;
    if (rt_value_as_int_wide(rt_any_add(text_boundary, rt_value_int(5))) != INT64_C(1152921504606846981)) return 48;
    if (rt_value_as_int_wide(rt_any_add(rt_value_int(5), text_boundary)) != INT64_C(1152921504606846981)) return 49;
    if (!text_equal(rt_any_add(rt_string_new((const uint8_t*)"n=", 2), text_min), "n=-9223372036854775808")) return 50;

    int64_t array = rt_array_new(4);
    if (array == 0 || rt_array_push(array, text_max) != 1 ||
        rt_array_push(array, text_min) != 1 ||
        rt_array_push(array, rt_value_int(INT64_MAX)) != 1 ||
        rt_array_push(array, rt_value_int(5)) != 1) return 51;
    if (rt_value_as_int_wide(rt_array_sum(array)) != INT64_MIN + 3) return 52;
    if (rt_value_as_int_wide(rt_array_min(array)) != INT64_MIN) return 53;
    if (rt_value_as_int_wide(rt_array_max(array)) != INT64_MAX) return 54;
    /* Fresh equal boxes must compare by signed value, not pointer identity. */
    if (rt_array_index_of(array, rt_value_int(INT64_MAX)) != 0) return 55;
    if (rt_array_last_index_of(array, rt_value_int(INT64_MAX)) != 2) return 56;
    if (rt_array_count(array, rt_value_int(INT64_MAX)) != 2) return 57;
    int64_t unique = rt_array_unique(array);
    if (rt_array_len(unique) != 3 || rt_value_as_int_wide(rt_array_get(unique, 0)) != INT64_MAX ||
        rt_value_as_int_wide(rt_array_get(unique, 1)) != INT64_MIN ||
        rt_value_as_int_wide(rt_array_get(unique, 2)) != 5) return 58;
    if (rt_array_sort(array) != 1 || rt_value_as_int_wide(rt_array_get(array, 0)) != INT64_MIN ||
        rt_value_as_int_wide(rt_array_get(array, 1)) != 5 ||
        rt_value_as_int_wide(rt_array_get(array, 2)) != INT64_MAX ||
        rt_value_as_int_wide(rt_array_get(array, 3)) != INT64_MAX) return 59;
    int64_t zero_array = rt_array_new(1);
    if (zero_array == 0 || rt_array_push(zero_array, rt_value_int_wide(0)) != 1) return 60;
    if (rt_array_index_of(zero_array, rt_value_int(0)) != 0 || rt_array_all_truthy(zero_array) != 0) return 61;
    rt_array_free(zero_array);
    rt_array_free(unique);
    rt_array_free(array);
    __simple_runtime_shutdown();
    return 0;
}
