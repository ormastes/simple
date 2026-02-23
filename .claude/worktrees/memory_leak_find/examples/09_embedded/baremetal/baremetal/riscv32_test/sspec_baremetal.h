/* SSpec Baremetal - Minimal test framework for semihosting output
 *
 * Provides describe/it/expect macros that output SSpec-compatible results
 * via semihosting, parseable by the Simple test runner.
 */
#ifndef SSPEC_BAREMETAL_H
#define SSPEC_BAREMETAL_H

#include "semihost.h"

/* Test counters */
static int _sspec_total = 0;
static int _sspec_passed = 0;
static int _sspec_failed = 0;

/* Current describe group */
static const char *_sspec_group = "";

/* Begin a describe group */
#define describe(name) do { \
    _sspec_group = name; \
    semihost_write0("\n"); \
    semihost_write0(name); \
    semihost_write0("\n"); \
} while(0)

/* Run a single test case */
#define it(name, body) do { \
    _sspec_total++; \
    int _test_ok = 1; \
    body; \
    if (_test_ok) { \
        _sspec_passed++; \
        semihost_write0("  \xe2\x9c\x93 "); \
        semihost_write0(name); \
        semihost_write0("\n"); \
    } \
} while(0)

/* Expect integer equality */
#define expect_equal(actual, expected) do { \
    if ((actual) != (expected)) { \
        _test_ok = 0; \
        _sspec_failed++; \
        semihost_write0("  \xe2\x9c\x97 FAIL: expected "); \
        semihost_print_int(expected); \
        semihost_write0(", got "); \
        semihost_print_int(actual); \
        semihost_write0("\n"); \
    } \
} while(0)

/* Expect condition is true */
#define expect_true(cond) do { \
    if (!(cond)) { \
        _test_ok = 0; \
        _sspec_failed++; \
        semihost_write0("  \xe2\x9c\x97 FAIL: condition was false\n"); \
    } \
} while(0)

/* Expect value is less than threshold */
#define expect_less_than(actual, threshold) do { \
    if ((actual) >= (threshold)) { \
        _test_ok = 0; \
        _sspec_failed++; \
        semihost_write0("  \xe2\x9c\x97 FAIL: "); \
        semihost_print_int(actual); \
        semihost_write0(" not less than "); \
        semihost_print_int(threshold); \
        semihost_write0("\n"); \
    } \
} while(0)

/* Print summary (SSpec format) */
#define sspec_summary() do { \
    semihost_write0("\n"); \
    semihost_print_int(_sspec_total); \
    semihost_write0(" examples, "); \
    semihost_print_int(_sspec_failed); \
    semihost_write0(" failures\n"); \
} while(0)

/* Return exit code based on results */
#define sspec_exit_code() (_sspec_failed > 0 ? 1 : 0)

#endif /* SSPEC_BAREMETAL_H */
