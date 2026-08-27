/*
 * Test-only C oracle for the RV32 SMP wait policy migrated to Pure Simple.
 * Provenance: the duplicated wait predicates in
 * src/os/kernel/arch/riscv32/{boot,fpga_boot}.spl at baseline revision
 * eb939043b9639e7e9bd8710fb9c6f859c1f727dc.
 * This file is never linked into a product or bootstrap runtime.
 */
#include <stdint.h>
#include <stdio.h>

static int run_c_hal_case(
    uint32_t online_harts,
    uint32_t spins,
    uint32_t expected_harts,
    uint32_t spin_limit
) {
    return online_harts < expected_harts && spins < spin_limit;
}

int main(void) {
    const int both_open = run_c_hal_case(2, 10, 3, 100);
    const int target_reached = run_c_hal_case(3, 10, 3, 100);
    const int budget_exhausted = run_c_hal_case(2, 100, 3, 100);
    const int failures = (both_open != 1) | (target_reached != 0) |
        (budget_exhausted != 0);
    printf("cases=%d,%d,%d\n", both_open, target_reached, budget_exhausted);
    return failures;
}
