/*
 * x86_64 (AMD64) CPU-specific tests.
 * Arch-specific calling-convention tests (rdi–r9 register passing,
 * 7th-arg stack spill) plus shared tests from test_cpu_common.h.
 *
 * x86_64 System V ABI key differences from ARM64:
 *   - 6 integer register args: rdi, rsi, rdx, rcx, r8, r9 (7th spills)
 *   - CALL pushes return address on stack (no link register)
 *   - 128-byte red zone below RSP
 *   - movabs loads full 64-bit immediate in one instruction
 *   - TSO memory model (stronger than ARM64's weakly ordered)
 *   - Callee-saved: rbx, rbp, r12–r15
 *
 * Included by test_platform.h when __x86_64__ is defined.
 */
#ifndef SPL_TEST_X86_64_H
#define SPL_TEST_X86_64_H

#include "test_cpu_common.h"

/* ================================================================
 * x86_64 calling convention helpers
 * System V ABI: rdi, rsi, rdx, rcx, r8, r9 (6 regs), 7th+ on stack
 * ================================================================ */

__attribute__((noinline))
static int64_t x64_sum6(int64_t a, int64_t b, int64_t c,
                         int64_t d, int64_t e, int64_t f) {
    return a + b + c + d + e + f;
}

__attribute__((noinline))
static int64_t x64_sum7(int64_t a, int64_t b, int64_t c, int64_t d,
                         int64_t e, int64_t f, int64_t g) {
    return a + b + c + d + e + f + g;
}

/* ================================================================
 * x86_64-specific tests (2)
 * ================================================================ */

TEST(x64_call_6_reg_args) {
    /* rdi, rsi, rdx, rcx, r8, r9: all 6 integer register arguments */
    int64_t r = x64_sum6(1, 2, 3, 4, 5, 6);
    ASSERT_EQ_INT(r, 21);
}

TEST(x64_call_7_args_stack_spill) {
    /* 7th arg spills to stack on x86_64 (vs 9th on ARM64) */
    int64_t r = x64_sum7(1, 2, 3, 4, 5, 6, 7);
    ASSERT_EQ_INT(r, 28);
}

/* ================================================================
 * Dispatcher — called from run_platform_tests()
 * 2 arch-specific + 39 common = 41 total
 * ================================================================ */

static void run_cpu_tests(void) {
    printf("\n--- x86_64: Calling Convention ---\n");
    RUN(x64_call_6_reg_args);
    RUN(x64_call_7_args_stack_spill);

    run_cpu_common_tests();
}

#endif /* SPL_TEST_X86_64_H */
