#include <stdbool.h>
#include <stdio.h>

enum { FSBL_OK = 0, FSBL_UNAVAILABLE = 1, FSBL_INVALID = 2, FSBL_HW_ERROR = 4 };
enum {
    SLCR_BASE = 0xF8000000U, DEVCFG_BASE = 0xF8007000U,
    LOCKSTA_OFFSET = 0x000CU, ARM_CLK_OFFSET = 0x0120U,
    DDR_CLK_OFFSET = 0x0124U, PSS_RST_OFFSET = 0x0200U,
    A9_RST_OFFSET = 0x0244U, DEVCFG_INT_STS_OFFSET = 0x000CU,
    SLCR_LOCKED = 0x00000001U, ARM_CLK_ACTIVE = 0x1F000000U,
    DDR_CLK_ACTIVE = 0x00000003U, PSS_PRIMARY_RESET = 0x00000001U,
    A9_CPU0_STOPPED = 0x00000111U, PCFG_DONE = 0x00000004U
};

int cosmos_fsbl_coverage_is_qemu;
static unsigned int mmio_read_count;
static unsigned int locksta, arm_clk, ddr_clk, pss_rst, a9_rst, devcfg_int_sts;

void cosmos_fsbl_coverage_reset(void);
unsigned long long cosmos_fsbl_coverage_mask(void);
unsigned long long cosmos_fsbl_coverage_required(void);
unsigned long long cosmos_fsbl_coverage_decisions(void);
int cosmos_fsbl_validate_handoff(void);
int cosmos_fsbl_selftest(void);

unsigned int cosmos_mmio_test_read32(unsigned int address) {
    mmio_read_count++;
    switch (address) {
    case SLCR_BASE + LOCKSTA_OFFSET: return locksta;
    case SLCR_BASE + ARM_CLK_OFFSET: return arm_clk;
    case SLCR_BASE + DDR_CLK_OFFSET: return ddr_clk;
    case SLCR_BASE + PSS_RST_OFFSET: return pss_rst;
    case SLCR_BASE + A9_RST_OFFSET: return a9_rst;
    case DEVCFG_BASE + DEVCFG_INT_STS_OFFSET: return devcfg_int_sts;
    default: return 0U;
    }
}

void cosmos_mmio_test_write32(unsigned int address, unsigned int value) {
    (void)address;
    (void)value;
}

static void valid_snapshot(void) {
    locksta = SLCR_LOCKED;
    arm_clk = ARM_CLK_ACTIVE;
    ddr_clk = DDR_CLK_ACTIVE;
    pss_rst = 0U;
    a9_rst = 0U;
    devcfg_int_sts = PCFG_DONE;
}

static int expect_status(const char *case_id, int actual, int expected) {
    if (actual == expected) return 0;
    fprintf(stderr, "%s: status=%d expected=%d\n", case_id, actual, expected);
    return 1;
}

int main(void) {
    unsigned long long mask, required;

    cosmos_fsbl_coverage_reset();
    valid_snapshot();
    cosmos_fsbl_coverage_is_qemu = 1;
    if (expect_status("bridge-qemu", cosmos_fsbl_validate_handoff(),
                      FSBL_UNAVAILABLE) || mmio_read_count != 0U) return 1;

    cosmos_fsbl_coverage_is_qemu = 0;
    if (expect_status("bridge-valid", cosmos_fsbl_validate_handoff(), FSBL_OK) ||
        mmio_read_count != 6U) return 1;

    locksta = 0U;
    if (expect_status("handoff-lock", cosmos_fsbl_validate_handoff(), FSBL_HW_ERROR)) return 1;
    valid_snapshot(); arm_clk = 0U;
    if (expect_status("handoff-arm", cosmos_fsbl_validate_handoff(), FSBL_HW_ERROR)) return 1;
    valid_snapshot(); ddr_clk = 0U;
    if (expect_status("handoff-ddr", cosmos_fsbl_validate_handoff(), FSBL_HW_ERROR)) return 1;
    valid_snapshot(); pss_rst = PSS_PRIMARY_RESET;
    if (expect_status("handoff-reset", cosmos_fsbl_validate_handoff(), FSBL_HW_ERROR)) return 1;
    valid_snapshot(); a9_rst = A9_CPU0_STOPPED;
    if (expect_status("handoff-cpu0", cosmos_fsbl_validate_handoff(), FSBL_HW_ERROR)) return 1;
    valid_snapshot(); devcfg_int_sts = 0U;
    if (expect_status("handoff-pcfg", cosmos_fsbl_validate_handoff(), FSBL_HW_ERROR)) return 1;
    valid_snapshot();

    if (expect_status("production-selftest", cosmos_fsbl_selftest(), FSBL_OK)) return 1;

    mask = cosmos_fsbl_coverage_mask();
    required = cosmos_fsbl_coverage_required();
    printf("COSMOS_FSBL_SIMPLE_RUNTIME_COVERAGE mask=%llu required=%llu "
           "decisions=%llu outcomes=24\n",
           mask, required, cosmos_fsbl_coverage_decisions());
    if (mask != required || required != 0x00FFFFFFULL ||
        cosmos_fsbl_coverage_decisions() != 12ULL) {
        fputs("pure-Simple production policy outcomes are incomplete\n", stderr);
        return 1;
    }
    puts("cosmos FSBL mixed C/Simple runtime coverage: PASS");
    return 0;
}
