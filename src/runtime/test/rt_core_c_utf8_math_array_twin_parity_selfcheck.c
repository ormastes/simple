/* Absolute-oracle parity probe for the six core-C-only lane twins added to
 * runtime_native.c on 2026-09-13: rt_math_sqrt, rt_utf8_validate,
 * rt_utf8_find_invalid, rt_utf8_count_codepoints, rt_numeric_dot_f64 and
 * rt_array_remove.
 *
 * WHY ABSOLUTE ORACLES, NOT A DIFF AGAINST THE RUST RUNTIME
 * The two lanes are never linked into one process -- that is the whole point
 * of the C-only CoreCBootstrap lane -- so a same-process A/B is impossible.
 * Every expectation below is therefore a value fixed by the specification
 * (IEEE-754, RFC 3629, arithmetic), independently asserted on the Simple side
 * by test/01_unit/runtime/c_lane_utf8_math_array_twin_parity_spec.spl running
 * on the seed INTERPRETER, i.e. against the Rust twin. Two lanes agreeing with
 * one written-down oracle is a stronger statement than two lanes agreeing with
 * each other.
 *
 * Build (links against the standalone-compiled runtime_native.o, i.e. the exact
 * TU the core-C bootstrap archive is made from -- same recipe as the
 * rt_bootstrap_c_lane_* selfchecks beside this file):
 *   cc -c -std=gnu11 -DSIMPLE_CORE_C_STANDALONE=1 \
 *      -Isrc/runtime -Isrc/runtime/platform src/runtime/runtime_native.c -o rn.o
 *   cc -std=gnu11 src/runtime/test/rt_core_c_utf8_math_array_twin_parity_selfcheck.c \
 *      rn.o -lpthread -lm -o selfcheck && ./selfcheck
 *
 * Exit status is the number of failures, and every failure prints its expected
 * and actual value. A run that executes zero checks is a failure too: a silent
 * exit 0 from a probe that checked nothing is the shape this repo has been
 * burned by before.
 */

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "runtime.h"

static int checks = 0;
static int failures = 0;

static void expect_i64(const char* what, int64_t actual, int64_t expected) {
    checks++;
    if (actual != expected) {
        failures++;
        printf("FAIL %s: expected %lld, got %lld\n", what, (long long)expected, (long long)actual);
    }
}

static void expect_f64_exact(const char* what, double actual, double expected) {
    checks++;
    /* Bit-exact: every oracle here is a correctly-rounded or exactly
     * representable value, so a tolerance would only hide a real defect. */
    if (memcmp(&actual, &expected, sizeof(double)) != 0) {
        failures++;
        printf("FAIL %s: expected %.17g, got %.17g\n", what, expected, actual);
    }
}

/* Build a generic (tagged-element) array of bytes, the shape a Simple `[u8]`
 * literal produces. */
static int64_t make_byte_array(const uint8_t* bytes, int64_t len) {
    SplArray* arr = rt_array_new(len > 0 ? len : 1);
    for (int64_t i = 0; i < len; i++) {
        rt_array_push(arr, rt_value_int((int64_t)bytes[i]));
    }
    return (int64_t)(uintptr_t)arr;
}

static int64_t make_f64_array(const double* values, int64_t len) {
    SplArray* arr = rt_array_new(len > 0 ? len : 1);
    for (int64_t i = 0; i < len; i++) {
        rt_array_push(arr, rt_value_float(values[i]));
    }
    return (int64_t)(uintptr_t)arr;
}

static int64_t make_int_array(const int64_t* values, int64_t len) {
    SplArray* arr = rt_array_new(len > 0 ? len : 1);
    for (int64_t i = 0; i < len; i++) {
        rt_array_push(arr, rt_value_int(values[i]));
    }
    return (int64_t)(uintptr_t)arr;
}

/* NIL is the tagged special 0 -- payload 0, TAG_SPECIAL 0b011 -- i.e. 3. */
#define RT_NIL_VALUE 3

static void check_sqrt(void) {
    /* sqrt(2) is the correctly-rounded double nearest to the true value; the
     * decimal below is that exact double. sqrt(4)=2 and sqrt(0)=0 are exact. */
    expect_f64_exact("rt_math_sqrt(2.0)", rt_math_sqrt(2.0), 1.4142135623730951);
    expect_f64_exact("rt_math_sqrt(4.0)", rt_math_sqrt(4.0), 2.0);
    expect_f64_exact("rt_math_sqrt(0.0)", rt_math_sqrt(0.0), 0.0);
    expect_f64_exact("rt_math_sqrt(1e100)", rt_math_sqrt(1e100), 1e50);
    checks++;
    if (!isnan(rt_math_sqrt(-1.0))) {
        failures++;
        printf("FAIL rt_math_sqrt(-1.0): expected NaN, got %.17g\n", rt_math_sqrt(-1.0));
    }

    /* The eight libm passthroughs added alongside sqrt. Only exactly
     * representable oracles are asserted bit-exactly; the transcendentals are
     * checked at arguments whose results are exact (sin(0)=0, cos(0)=1,
     * tan(0)=0, exp(0)=1, cbrt(8)=2, hypot(3,4)=5) so no tolerance is needed
     * and no rounding-mode assumption is smuggled in. */
    expect_f64_exact("rt_math_exp(0.0)", rt_math_exp(0.0), 1.0);
    expect_f64_exact("rt_math_exp(1.0)", rt_math_exp(1.0), 2.7182818284590451);
    expect_f64_exact("rt_math_cbrt(8.0)", rt_math_cbrt(8.0), 2.0);
    expect_f64_exact("rt_math_cbrt(-27.0)", rt_math_cbrt(-27.0), -3.0);
    expect_f64_exact("rt_math_sin(0.0)", rt_math_sin(0.0), 0.0);
    expect_f64_exact("rt_math_cos(0.0)", rt_math_cos(0.0), 1.0);
    expect_f64_exact("rt_math_tan(0.0)", rt_math_tan(0.0), 0.0);
    expect_f64_exact("rt_math_hypot(3.0,4.0)", rt_math_hypot(3.0, 4.0), 5.0);

    /* min/max are IEEE minNum/maxNum: ordinary ordering, and the NON-NaN
     * operand wins when exactly one side is NaN. A `a < b ? a : b` spelling
     * would propagate the NaN instead and is the defect this pins. */
    expect_f64_exact("rt_math_min(2.0,3.0)", rt_math_min(2.0, 3.0), 2.0);
    expect_f64_exact("rt_math_max(2.0,3.0)", rt_math_max(2.0, 3.0), 3.0);
    expect_f64_exact("rt_math_min(-1.0,1.0)", rt_math_min(-1.0, 1.0), -1.0);
    expect_f64_exact("rt_math_min(NaN,3.0)", rt_math_min(NAN, 3.0), 3.0);
    expect_f64_exact("rt_math_max(NaN,3.0)", rt_math_max(NAN, 3.0), 3.0);
    expect_f64_exact("rt_math_min(3.0,NaN)", rt_math_min(3.0, NAN), 3.0);
    expect_f64_exact("rt_math_max(3.0,NaN)", rt_math_max(3.0, NAN), 3.0);
}

struct utf8_case {
    const char* name;
    const uint8_t bytes[8];
    int64_t len;
    int64_t valid;        /* rt_utf8_validate */
    int64_t first_invalid; /* rt_utf8_find_invalid: -1 when valid */
    int64_t codepoints;    /* rt_utf8_count_codepoints */
};

static void check_utf8(void) {
    /* Every `first_invalid` below is the offset of the FIRST BYTE of the
     * offending sequence (Rust's Utf8Error::valid_up_to), not of the offending
     * byte itself. `codepoints` follows the lead-byte walk, which is defined on
     * malformed input too and is deliberately NOT validation. */
    static const struct utf8_case cases[] = {
        {"empty",            {0},                              0, 1, -1, 0},
        {"ascii abc",        {0x61, 0x62, 0x63},               3, 1, -1, 3},
        {"h e-acute l l o",  {0x68, 0xC3, 0xA9, 0x6C, 0x6C, 0x6F}, 6, 1, -1, 5},
        {"euro sign",        {0xE2, 0x82, 0xAC},               3, 1, -1, 1},
        {"U+10348 4-byte",   {0xF0, 0x90, 0x8D, 0x88},         4, 1, -1, 1},
        {"U+10FFFF max",     {0xF4, 0x8F, 0xBF, 0xBF},         4, 1, -1, 1},
        /* Invalid: lone 0xFF is never a lead byte, at offset 1. */
        {"a then 0xFF",      {0x61, 0xFF},                     2, 0,  1, 2},
        /* Invalid: 2-byte lead followed by a non-continuation. */
        {"C3 28",            {0xC3, 0x28},                     2, 0,  0, 1},
        /* Invalid: truncated 3-byte sequence -- reported at its start. */
        {"E2 82 truncated",  {0xE2, 0x82},                     2, 0,  0, 1},
        /* Invalid: UTF-16 surrogate U+D800, banned by RFC 3629. */
        {"ED A0 80 surrogate", {0xED, 0xA0, 0x80},             3, 0,  0, 1},
        /* Invalid: overlong 2-byte encoding of '/'. */
        {"C0 AF overlong",   {0xC0, 0xAF},                     2, 0,  0, 1},
        /* Invalid: overlong 4-byte encoding of U+20AC. */
        {"F0 82 82 AC overlong", {0xF0, 0x82, 0x82, 0xAC},     4, 0,  0, 1},
        /* Invalid: U+110000, one past the Unicode maximum. */
        {"F4 90 80 80 too big", {0xF4, 0x90, 0x80, 0x80},      4, 0,  0, 1},
        /* Invalid: a bare continuation byte with no lead. */
        {"bare 0x80",        {0x80},                           1, 0,  0, 1},
        /* Invalid at a non-zero offset, after two valid codepoints. */
        {"ok ok then bad",   {0x61, 0xC3, 0xA9, 0xC3, 0x28},   5, 0,  3, 3},
    };
    const int n = (int)(sizeof(cases) / sizeof(cases[0]));
    for (int i = 0; i < n; i++) {
        int64_t value = make_byte_array(cases[i].bytes, cases[i].len);
        char label[128];
        snprintf(label, sizeof(label), "rt_utf8_validate(%s)", cases[i].name);
        expect_i64(label, (int64_t)rt_utf8_validate(value), cases[i].valid);
        snprintf(label, sizeof(label), "rt_utf8_find_invalid(%s)", cases[i].name);
        expect_i64(label, rt_utf8_find_invalid(value), cases[i].first_invalid);
        snprintf(label, sizeof(label), "rt_utf8_count_codepoints(%s)", cases[i].name);
        expect_i64(label, rt_utf8_count_codepoints(value), cases[i].codepoints);
    }

    /* Refusal convention, mirrored from the Rust twin's `else` arms: a
     * non-array argument is false / 0 / 0, and find_invalid's 0 deliberately
     * collides with "invalid at offset 0". */
    expect_i64("rt_utf8_validate(nil)", (int64_t)rt_utf8_validate(RT_NIL_VALUE), 0);
    expect_i64("rt_utf8_find_invalid(nil)", rt_utf8_find_invalid(RT_NIL_VALUE), 0);
    expect_i64("rt_utf8_count_codepoints(nil)", rt_utf8_count_codepoints(RT_NIL_VALUE), 0);
}

static void check_dot(void) {
    static const double a3[] = {1.0, 2.0, 3.0};
    static const double b3[] = {4.0, 5.0, 6.0};
    /* 1*4 + 2*5 + 3*6 = 32, exactly representable. */
    expect_f64_exact("dot([1,2,3],[4,5,6])",
                     rt_value_as_float(rt_numeric_dot_f64(make_f64_array(a3, 3), make_f64_array(b3, 3))),
                     32.0);

    static const double zero3[] = {0.0, 0.0, 0.0};
    expect_f64_exact("dot([1,2,3],[0,0,0])",
                     rt_value_as_float(rt_numeric_dot_f64(make_f64_array(a3, 3), make_f64_array(zero3, 3))),
                     0.0);

    /* Mixed int/float operands: integers widen, same as the Rust twin. */
    static const int64_t i3[] = {2, 3, 4};
    expect_f64_exact("dot([1,2,3] f64, [2,3,4] int)",
                     rt_value_as_float(rt_numeric_dot_f64(make_f64_array(a3, 3), make_int_array(i3, 3))),
                     20.0);

    /* An empty pair is 0.0, not NIL -- the loop simply does not run. */
    expect_f64_exact("dot([],[])",
                     rt_value_as_float(rt_numeric_dot_f64(make_f64_array(a3, 0), make_f64_array(b3, 0))),
                     0.0);

    /* Length mismatch and a non-array receiver are NIL, never 0.0: a 0.0 would
     * read as a legitimate dot product of orthogonal vectors. */
    expect_i64("dot(len 3, len 2) is nil",
               rt_numeric_dot_f64(make_f64_array(a3, 3), make_f64_array(b3, 2)), RT_NIL_VALUE);
    expect_i64("dot(nil, [4,5,6]) is nil",
               rt_numeric_dot_f64(RT_NIL_VALUE, make_f64_array(b3, 3)), RT_NIL_VALUE);
}

static void check_array_remove(void) {
    static const int64_t src[] = {10, 20, 30, 40};

    /* Remove at index 0: returns the removed element, shifts the tail down. */
    int64_t arr = make_int_array(src, 4);
    expect_i64("remove(0) returns 10", rt_array_remove(arr, 0), rt_value_int(10));
    expect_i64("len after remove(0)", rt_array_len_safe(arr), 3);
    expect_i64("arr[0] after remove(0)", rt_array_get((SplArray*)(uintptr_t)arr, 0), rt_value_int(20));
    expect_i64("arr[2] after remove(0)", rt_array_get((SplArray*)(uintptr_t)arr, 2), rt_value_int(40));

    /* Remove in the middle. */
    arr = make_int_array(src, 4);
    expect_i64("remove(1) returns 20", rt_array_remove(arr, 1), rt_value_int(20));
    expect_i64("len after remove(1)", rt_array_len_safe(arr), 3);
    expect_i64("arr[1] after remove(1)", rt_array_get((SplArray*)(uintptr_t)arr, 1), rt_value_int(30));

    /* Remove the last element. */
    arr = make_int_array(src, 4);
    expect_i64("remove(3) returns 40", rt_array_remove(arr, 3), rt_value_int(40));
    expect_i64("len after remove(3)", rt_array_len_safe(arr), 3);
    expect_i64("arr[2] after remove(3)", rt_array_get((SplArray*)(uintptr_t)arr, 2), rt_value_int(30));

    /* Out of range in both directions is NIL and leaves the array untouched.
     * A negative index does NOT count from the end here, unlike rt_array_get. */
    arr = make_int_array(src, 4);
    expect_i64("remove(4) is nil", rt_array_remove(arr, 4), RT_NIL_VALUE);
    expect_i64("remove(-1) is nil", rt_array_remove(arr, -1), RT_NIL_VALUE);
    expect_i64("len unchanged after refusals", rt_array_len_safe(arr), 4);

    /* Removing the only element leaves an empty array. */
    static const int64_t one[] = {7};
    arr = make_int_array(one, 1);
    expect_i64("remove(0) of single returns 7", rt_array_remove(arr, 0), rt_value_int(7));
    expect_i64("len after emptying", rt_array_len_safe(arr), 0);
    expect_i64("remove(0) of empty is nil", rt_array_remove(arr, 0), RT_NIL_VALUE);

    /* A non-array receiver is NIL. */
    expect_i64("remove on nil is nil", rt_array_remove(RT_NIL_VALUE, 0), RT_NIL_VALUE);
}

int main(void) {
    check_sqrt();
    check_utf8();
    check_dot();
    check_array_remove();

    if (checks == 0) {
        printf("FAIL — nothing was checked\n");
        return 1;
    }
    printf("%s — %d check(s), %d failure(s)\n", failures == 0 ? "PASS" : "FAIL", checks, failures);
    return failures == 0 ? 0 : failures;
}
