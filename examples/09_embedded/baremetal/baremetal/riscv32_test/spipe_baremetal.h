/* SPipe Baremetal - Minimal test framework for semihosting output
 *
 * Provides describe/it/expect macros that output SPipe-compatible results
 * via semihosting, parseable by the Simple test runner.
 */
#ifndef SPIPE_BAREMETAL_H
#define SPIPE_BAREMETAL_H

#include "semihost.h"

/* Test counters */
static int _spipe_total = 0;
static int _spipe_passed = 0;
static int _spipe_failed = 0;

/* Current describe group */
static const char *_spipe_group = "";

/* Begin a describe group */
#define describe(name) do { \
    _spipe_group = name; \
    semihost_write0("\n"); \
    semihost_write0(name); \
    semihost_write0("\n"); \
} while(0)

/* Run a single test case */
#define it(name, body) do { \
    _spipe_total++; \
    int _test_ok = 1; \
    body; \
    if (_test_ok) { \
        _spipe_passed++; \
        semihost_write0("  \xe2\x9c\x93 "); \
        semihost_write0(name); \
        semihost_write0("\n"); \
    } \
} while(0)

/* Expect integer equality */
#define expect_equal(actual, expected) do { \
    if ((actual) != (expected)) { \
        _test_ok = 0; \
        _spipe_failed++; \
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
        _spipe_failed++; \
        semihost_write0("  \xe2\x9c\x97 FAIL: condition was false\n"); \
    } \
} while(0)

/* Expect value is less than threshold */
#define expect_less_than(actual, threshold) do { \
    if ((actual) >= (threshold)) { \
        _test_ok = 0; \
        _spipe_failed++; \
        semihost_write0("  \xe2\x9c\x97 FAIL: "); \
        semihost_print_int(actual); \
        semihost_write0(" not less than "); \
        semihost_print_int(threshold); \
        semihost_write0("\n"); \
    } \
} while(0)

/* Print summary (SPipe format) */
#define spipe_summary() do { \
    semihost_write0("\n"); \
    semihost_print_int(_spipe_total); \
    semihost_write0(" examples, "); \
    semihost_print_int(_spipe_failed); \
    semihost_write0(" failures\n"); \
} while(0)

/* Return exit code based on results */
#define spipe_exit_code() (_spipe_failed > 0 ? 1 : 0)

#endif /* SPIPE_BAREMETAL_H */
