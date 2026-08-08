/* Cosmos+ FSBL handoff checks for Zynq-7000.
 *
 * The FSBL owns clocks, DDR, and reset sequencing. The kernel observes that
 * handoff and does not repeat it: these checks are read-only by design.
 */
#include "cosmos_hal.h"
#include "cosmos_zynq_regs.h"

#define COSMOS_SLCR_LOCKED    (1U << 0)
#define COSMOS_ARM_CLK_ACTIVE (0x1FU << 24)
#define COSMOS_DDR_CLK_ACTIVE ((1U << 0) | (1U << 1))
#define COSMOS_PSS_PRIMARY_RESET (1U << 0)
#define COSMOS_A9_CPU0_STOPPED ((1U << 0) | (1U << 4) | (1U << 8))

#if !COSMOS_IS_QEMU
static unsigned int cosmos_fsbl_read_slcr(unsigned int offset) {
    return cosmos_mmio_read32(COSMOS_SLCR_BASE + offset);
}

static unsigned int cosmos_fsbl_read_devcfg(unsigned int offset) {
    return cosmos_mmio_read32(COSMOS_ZYNQ_DEVCFG_BASE + offset);
}
#endif

static int cosmos_fsbl_handoff_valid(unsigned int locksta,
                                     unsigned int arm_clk,
                                     unsigned int ddr_clk,
                                     unsigned int pss_rst,
                                     unsigned int a9_rst,
                                     unsigned int devcfg_int_sts) {
    if ((locksta & COSMOS_SLCR_LOCKED) == 0U) {
        return 0;
    }
    if ((arm_clk & COSMOS_ARM_CLK_ACTIVE) != COSMOS_ARM_CLK_ACTIVE ||
        (ddr_clk & COSMOS_DDR_CLK_ACTIVE) != COSMOS_DDR_CLK_ACTIVE) {
        return 0;
    }
    if ((pss_rst & COSMOS_PSS_PRIMARY_RESET) != 0U ||
        (a9_rst & COSMOS_A9_CPU0_STOPPED) != 0U) {
        return 0;
    }
    return cosmos_zynq_pcfg_done(devcfg_int_sts);
}

int cosmos_fsbl_validate_handoff(void) {
#if COSMOS_IS_QEMU
    return COSMOS_UNAVAILABLE;
#else
    unsigned int locksta =
        cosmos_fsbl_read_slcr(COSMOS_ZYNQ_SLCR_LOCKSTA_OFFSET);
    unsigned int arm_clk =
        cosmos_fsbl_read_slcr(COSMOS_ZYNQ_SLCR_ARM_CLK_OFFSET);
    unsigned int ddr_clk =
        cosmos_fsbl_read_slcr(COSMOS_ZYNQ_SLCR_DDR_CLK_OFFSET);
    unsigned int pss_rst =
        cosmos_fsbl_read_slcr(COSMOS_ZYNQ_SLCR_PSS_RST_OFFSET);
    unsigned int a9_rst =
        cosmos_fsbl_read_slcr(COSMOS_ZYNQ_SLCR_A9_RST_OFFSET);
    unsigned int devcfg_int_sts =
        cosmos_fsbl_read_devcfg(COSMOS_ZYNQ_DEVCFG_INT_STS_OFFSET);

    return cosmos_fsbl_handoff_valid(locksta, arm_clk, ddr_clk, pss_rst,
                                     a9_rst, devcfg_int_sts)
        ? COSMOS_OK : COSMOS_HW_ERROR;
#endif
}

int cosmos_fsbl_selftest(void) {
    const unsigned int good_arm_clk = COSMOS_ARM_CLK_ACTIVE;
    const unsigned int good_ddr_clk = COSMOS_DDR_CLK_ACTIVE;
    const unsigned int good_pcfg = COSMOS_ZYNQ_DEVCFG_PCFG_DONE;

    if (COSMOS_ZYNQ_SLCR_ARM_CLK_OFFSET != 0x0120U ||
        COSMOS_ZYNQ_SLCR_DDR_CLK_OFFSET != 0x0124U) {
        return COSMOS_INVALID;
    }
    if (!cosmos_fsbl_handoff_valid(COSMOS_SLCR_LOCKED, good_arm_clk,
                                   good_ddr_clk, 0U, 0U, good_pcfg)) {
        return COSMOS_INVALID;
    }
    if (cosmos_fsbl_handoff_valid(COSMOS_SLCR_LOCKED, good_arm_clk,
                                  good_ddr_clk, 0U, 0U, 0U)) {
        return COSMOS_INVALID;
    }
    return COSMOS_OK;
}
