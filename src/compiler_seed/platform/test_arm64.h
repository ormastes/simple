/*
 * ARM64 (AArch64) CPU-specific tests.
 * Arch-specific calling-convention tests (x0–x7 register passing,
 * 9th-arg stack spill) plus shared tests from test_cpu_common.h.
 *
 * Included by test_platform.h when __aarch64__ is defined.
 */
#ifndef SPL_TEST_ARM64_H
#define SPL_TEST_ARM64_H

#include "test_cpu_common.h"

/* ================================================================
 * ARM64 calling convention helpers
 * ARM64 ABI: x0–x7 for integer args (8 regs), 9th+ spill to stack
 * ================================================================ */

__attribute__((noinline))
static int64_t arm64_sum8(int64_t a, int64_t b, int64_t c, int64_t d,
                          int64_t e, int64_t f, int64_t g, int64_t h) {
    return a + b + c + d + e + f + g + h;
}

__attribute__((noinline))
static int64_t arm64_sum9(int64_t a, int64_t b, int64_t c, int64_t d,
                          int64_t e, int64_t f, int64_t g, int64_t h,
                          int64_t i) {
    return a + b + c + d + e + f + g + h + i;
}

/* ================================================================
 * ARM64-specific tests (2)
 * ================================================================ */

TEST(arm64_call_8_reg_args) {
    /* x0–x7: all 8 integer register arguments */
    int64_t r = arm64_sum8(1, 2, 3, 4, 5, 6, 7, 8);
    ASSERT_EQ_INT(r, 36);
}

TEST(arm64_call_9_args_stack_spill) {
    /* 9th arg spills to stack on ARM64 */
    int64_t r = arm64_sum9(1, 2, 3, 4, 5, 6, 7, 8, 9);
    ASSERT_EQ_INT(r, 45);
}

/* ================================================================
 * Dispatcher — called from run_platform_tests()
 * 2 arch-specific + 39 common = 41 total
 * ================================================================ */

static void run_cpu_tests(void) {
    printf("\n--- ARM64: Calling Convention ---\n");
    RUN(arm64_call_8_reg_args);
    RUN(arm64_call_9_args_stack_spill);

    run_cpu_common_tests();
}

#endif /* SPL_TEST_ARM64_H */
