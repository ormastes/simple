/*
 * Test dispatcher — picks the correct platform test header.
 * Included by runtime_test.c after test macros (TEST/RUN/ASSERT) are defined.
 */
#ifndef SPL_TEST_PLATFORM_H
#define SPL_TEST_PLATFORM_H

/* CPU architecture tests (defines run_cpu_tests) */
#if defined(__aarch64__)
#  include "test_arm64.h"
#elif defined(__x86_64__)
#  include "test_x86_64.h"
#else
static void run_cpu_tests(void) {}
#endif

/* OS-specific tests (run_platform_tests calls run_cpu_tests) */
#if defined(_WIN32)
#  include "test_platform_win.h"
#elif defined(__APPLE__) || defined(__FreeBSD__) || defined(__linux__)
#  include "test_unix_common.h"
#endif

#endif /* SPL_TEST_PLATFORM_H */
