#ifndef SIMPLE_COSMOS_ZYNQ_REGS_H
#define SIMPLE_COSMOS_ZYNQ_REGS_H

/* Zynq-7000 PS register definitions from UG585. */
#define COSMOS_ZYNQ_DEVCFG_BASE            0xF8007000U
#define COSMOS_ZYNQ_DEVCFG_INT_STS_OFFSET  0x000CU
#define COSMOS_ZYNQ_DEVCFG_PCFG_DONE       (1U << 2)

#define COSMOS_ZYNQ_SLCR_LOCKSTA_OFFSET     0x000CU
#define COSMOS_ZYNQ_SLCR_ARM_CLK_OFFSET     0x0120U
#define COSMOS_ZYNQ_SLCR_DDR_CLK_OFFSET     0x0124U
#define COSMOS_ZYNQ_SLCR_PSS_RST_OFFSET     0x0200U
#define COSMOS_ZYNQ_SLCR_A9_RST_OFFSET      0x0244U

static inline int cosmos_zynq_pcfg_done(unsigned int interrupt_status) {
    return (interrupt_status & COSMOS_ZYNQ_DEVCFG_PCFG_DONE) != 0U;
}

#endif
