/* Native acquisition boundary for the pure-Simple Cosmos+ FSBL policy.
 *
 * cosmos_fsbl.spl owns validation, status mapping, and the self-test.  This
 * file deliberately retains only the two operations that require the C HAL:
 * selecting the build environment and reading one 32-bit MMIO register.
 */
#include "cosmos_hal.h"

/* Handoff oracle masks. The test-only oracle extraction
 * (test/fixtures/os/cosmos/cosmos_fsbl_oracle.c) and the host MMIO runner
 * fail closed unless the text from the first include through EOF matches this
 * file exactly; keep these in lockstep with cosmos_fsbl_decision.spl. */
#define COSMOS_SLCR_LOCKED    (1U << 0)
#define COSMOS_ARM_CLK_ACTIVE (0x1FU << 24)
#define COSMOS_DDR_CLK_ACTIVE ((1U << 0) | (1U << 1))
#define COSMOS_PSS_PRIMARY_RESET (1U << 0)
#define COSMOS_A9_CPU0_STOPPED ((1U << 0) | (1U << 4) | (1U << 8))

/* Coverage builds replace the compile-time environment constant with a
 * mutable test seam.  The production build still folds this expression to
 * COSMOS_IS_QEMU, while the instrumented host build executes both outcomes of
 * the same bridge decision without touching physical MMIO. */
#if defined(COSMOS_FSBL_COVERAGE_TEST)
extern int cosmos_fsbl_coverage_is_qemu;
#define COSMOS_FSBL_BRIDGE_IS_QEMU cosmos_fsbl_coverage_is_qemu

extern void __cosmos_fsbl_policy_coverage_reset(void);
extern unsigned long long __cosmos_fsbl_policy_coverage_mask(void);
extern unsigned long long __cosmos_fsbl_policy_coverage_required(void);
extern unsigned long long __cosmos_fsbl_policy_coverage_decisions(void);

void cosmos_fsbl_coverage_reset(void) {
    __cosmos_fsbl_policy_coverage_reset();
}

unsigned long long cosmos_fsbl_coverage_mask(void) {
    return __cosmos_fsbl_policy_coverage_mask();
}

unsigned long long cosmos_fsbl_coverage_required(void) {
    return __cosmos_fsbl_policy_coverage_required();
}

unsigned long long cosmos_fsbl_coverage_decisions(void) {
    return __cosmos_fsbl_policy_coverage_decisions();
}
#else
#define COSMOS_FSBL_BRIDGE_IS_QEMU COSMOS_IS_QEMU
#endif

int cosmos_fsbl_bridge_is_qemu(void) {
    return COSMOS_FSBL_BRIDGE_IS_QEMU;
}

unsigned int cosmos_fsbl_bridge_read32(unsigned int address) {
    if (!COSMOS_FSBL_BRIDGE_IS_QEMU) {
        return cosmos_mmio_read32(address);
    }
    (void)address;
    return 0U;
}
