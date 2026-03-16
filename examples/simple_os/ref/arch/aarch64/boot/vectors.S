/*
 * vectors.S — AArch64 EL1 exception vector table
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * AArch64 exception vector table layout:
 *   4 groups x 4 entries = 16 entries, each 128 bytes (32 instructions)
 *
 * Groups:
 *   Current EL with SP_EL0  (EL1t)   — unused in kernel
 *   Current EL with SP_ELx  (EL1h)   — kernel exceptions
 *   Lower EL using AArch64  (EL0_64) — user-mode traps
 *   Lower EL using AArch32  (EL0_32) — not supported
 *
 * Entry types per group:
 *   Synchronous, IRQ, FIQ, SError
 */

.extern exception_handler

/* ══════════════════════════════════════════════════════════════════════
 * Trap frame save / restore macros
 *
 * trap_frame layout (on stack):
 *   [sp+  0] x0
 *   [sp+  8] x1
 *   ...
 *   [sp+240] x30
 *   [sp+248] sp (saved user/kernel sp)
 *   [sp+256] elr_el1
 *   [sp+264] spsr_el1
 *   [sp+272] esr_el1
 *   [sp+280] far_el1
 * Total: 288 bytes (36 x 8)
 * ══════════════════════════════════════════════════════════════════════ */

.macro SAVE_REGS
    /* Allocate trap frame on stack */
    sub     sp, sp, #288

    /* Save x0-x30 */
    stp     x0,  x1,  [sp, #0]
    stp     x2,  x3,  [sp, #16]
    stp     x4,  x5,  [sp, #32]
    stp     x6,  x7,  [sp, #48]
    stp     x8,  x9,  [sp, #64]
    stp     x10, x11, [sp, #80]
    stp     x12, x13, [sp, #96]
    stp     x14, x15, [sp, #112]
    stp     x16, x17, [sp, #128]
    stp     x18, x19, [sp, #144]
    stp     x20, x21, [sp, #160]
    stp     x22, x23, [sp, #176]
    stp     x24, x25, [sp, #192]
    stp     x26, x27, [sp, #208]
    stp     x28, x29, [sp, #224]
    str     x30,      [sp, #240]

    /* Save special registers */
    mrs     x0, elr_el1
    mrs     x1, spsr_el1
    mrs     x2, esr_el1
    mrs     x3, far_el1

    /* Save the original SP (before sub) */
    add     x4, sp, #288
    str     x4,  [sp, #248]

    stp     x0,  x1,  [sp, #256]
    stp     x2,  x3,  [sp, #272]
.endm

.macro RESTORE_REGS
    /* Restore special registers */
    ldp     x0,  x1,  [sp, #256]
    msr     elr_el1,  x0
    msr     spsr_el1, x1

    /* Restore x0-x30 */
    ldp     x0,  x1,  [sp, #0]
    ldp     x2,  x3,  [sp, #16]
    ldp     x4,  x5,  [sp, #32]
    ldp     x6,  x7,  [sp, #48]
    ldp     x8,  x9,  [sp, #64]
    ldp     x10, x11, [sp, #80]
    ldp     x12, x13, [sp, #96]
    ldp     x14, x15, [sp, #112]
    ldp     x16, x17, [sp, #128]
    ldp     x18, x19, [sp, #144]
    ldp     x20, x21, [sp, #160]
    ldp     x22, x23, [sp, #176]
    ldp     x24, x25, [sp, #192]
    ldp     x26, x27, [sp, #208]
    ldp     x28, x29, [sp, #224]
    ldr     x30,      [sp, #240]

    /* Deallocate trap frame */
    add     sp, sp, #288
.endm

/* ── Vector entry macro ───────────────────────────────────────────── */

.macro VECTOR_ENTRY label
    .balign 128
\label:
    SAVE_REGS
    mov     x0, sp              /* x0 = pointer to trap_frame_t */
    bl      exception_handler
    RESTORE_REGS
    eret
.endm

.macro VECTOR_ENTRY_INVALID label
    .balign 128
\label:
    SAVE_REGS
    mov     x0, sp
    bl      exception_handler
    RESTORE_REGS
    eret
.endm

/* ══════════════════════════════════════════════════════════════════════
 * Vector table — must be 2048-byte aligned
 * ══════════════════════════════════════════════════════════════════════ */

.section .vectors, "ax"
.global vectors
.balign 2048

vectors:

/* ── Current EL with SP_EL0 (EL1t) ────────────────────────────────── */
    VECTOR_ENTRY_INVALID    el1t_sync
    VECTOR_ENTRY_INVALID    el1t_irq
    VECTOR_ENTRY_INVALID    el1t_fiq
    VECTOR_ENTRY_INVALID    el1t_serror

/* ── Current EL with SP_ELx (EL1h) — kernel mode ──────────────────── */
    VECTOR_ENTRY            el1h_sync
    VECTOR_ENTRY            el1h_irq
    VECTOR_ENTRY_INVALID    el1h_fiq
    VECTOR_ENTRY            el1h_serror

/* ── Lower EL using AArch64 (EL0_64) — user mode ──────────────────── */
    VECTOR_ENTRY            el0_64_sync
    VECTOR_ENTRY            el0_64_irq
    VECTOR_ENTRY_INVALID    el0_64_fiq
    VECTOR_ENTRY            el0_64_serror

/* ── Lower EL using AArch32 (EL0_32) — not supported ──────────────── */
    VECTOR_ENTRY_INVALID    el0_32_sync
    VECTOR_ENTRY_INVALID    el0_32_irq
    VECTOR_ENTRY_INVALID    el0_32_fiq
    VECTOR_ENTRY_INVALID    el0_32_serror
