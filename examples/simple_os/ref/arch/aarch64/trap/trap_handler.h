/*
 * trap_handler.h — Exception dispatch for AArch64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 */

#ifndef ARCH_AARCH64_TRAP_TRAP_HANDLER_H
#define ARCH_AARCH64_TRAP_TRAP_HANDLER_H

#include "common/types.h"
#include "common/config.h"
#include "common/compiler.h"

/* ── Trap frame (matches vectors.S SAVE_REGS layout) ───────────────── */

typedef struct {
    uint64_t x[31];         /* x0-x30                              */
    uint64_t sp;            /* Saved stack pointer                  */
    uint64_t elr_el1;       /* Exception Link Register              */
    uint64_t spsr_el1;      /* Saved Program Status Register        */
    uint64_t esr_el1;       /* Exception Syndrome Register          */
    uint64_t far_el1;       /* Fault Address Register               */
} trap_frame_t;

/* ── ESR_EL1 Exception Class (EC) values ───────────────────────────── */

#define ESR_EC_SHIFT        26
#define ESR_EC_MASK         (0x3FUL << ESR_EC_SHIFT)

#define EC_UNKNOWN          0x00    /* Unknown reason                  */
#define EC_WFI_WFE          0x01    /* Trapped WFI/WFE                 */
#define EC_SVC_AARCH64      0x15    /* SVC instruction (AArch64)       */
#define EC_HVC_AARCH64      0x16    /* HVC instruction (AArch64)       */
#define EC_SMC_AARCH64      0x17    /* SMC instruction (AArch64)       */
#define EC_SYSREG           0x18    /* MSR/MRS/System instruction      */
#define EC_IABT_LOWER_EL    0x20    /* Instruction Abort (lower EL)    */
#define EC_IABT_CURRENT_EL  0x21    /* Instruction Abort (current EL)  */
#define EC_PC_ALIGN          0x22    /* PC alignment fault              */
#define EC_DABT_LOWER_EL    0x24    /* Data Abort (lower EL)           */
#define EC_DABT_CURRENT_EL  0x25    /* Data Abort (current EL)         */
#define EC_SP_ALIGN          0x26    /* SP alignment fault              */
#define EC_FP_AARCH64       0x2C    /* FP exception (AArch64)          */
#define EC_SERROR           0x2F    /* SError                          */
#define EC_BRK              0x3C    /* BRK instruction (AArch64)       */

/* ── ISS (Instruction Specific Syndrome) helpers ───────────────────── */

#define ESR_ISS_MASK        0x01FFFFFF

/* SVC immediate value (for syscall number) */
#define ESR_SVC_IMM(esr)    ((esr) & 0xFFFF)

/* Data/Instruction Abort ISS fields */
#define ISS_DFSC_MASK       0x3F        /* Data Fault Status Code      */
#define ISS_WNR             (1 << 6)    /* Write not Read              */
#define ISS_CM              (1 << 8)    /* Cache maintenance           */

/* ── Maximum handler counts ────────────────────────────────────────── */

#define NUM_IRQ_HANDLERS    256

/* ── Handler function pointer types ────────────────────────────────── */

typedef void (*irq_handler_t)(trap_frame_t *frame);
typedef void (*exception_handler_t)(trap_frame_t *frame);

/* ── Public API ────────────────────────────────────────────────────── */

/* Called from vectors.S */
void exception_handler(trap_frame_t *frame);

/* Register handlers */
void register_irq_handler(uint32_t irq, irq_handler_t handler);
void register_sync_handler(uint32_t ec, exception_handler_t handler);

#endif /* ARCH_AARCH64_TRAP_TRAP_HANDLER_H */
