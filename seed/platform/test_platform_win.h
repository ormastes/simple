/*
 * Windows-specific test cases — stubs for now.
 *
 * Included by runtime_test.c via test_platform.h.
 * Requires TEST/RUN/ASSERT macros to be defined before inclusion.
 */
#ifndef SPL_TEST_PLATFORM_WIN_H
#define SPL_TEST_PLATFORM_WIN_H

/* No Windows-specific tests yet */

static void run_platform_tests(void) {
    printf("\n--- Platform Tests (Windows): skipped ---\n");

    run_cpu_tests();
}

#endif /* SPL_TEST_PLATFORM_WIN_H */
