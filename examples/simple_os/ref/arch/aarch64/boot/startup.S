/*
 * startup.S — AArch64 boot entry point
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Boot sequence:
 *   1. Check current EL, drop from EL2 to EL1 if needed
 *   2. Set VBAR_EL1 (exception vector base)
 *   3. Set up initial kernel stack
 *   4. Zero BSS
 *   5. Call kernel_main
 *   6. WFE loop if kernel_main returns
 */

.set STACK_SIZE, 16384      /* 16 KB kernel stack */

/* ══════════════════════════════════════════════════════════════════════
 * Entry point
 * ══════════════════════════════════════════════════════════════════════ */

.section .text.boot
.global _start
.type _start, @function

_start:
    /* ── Check current exception level ──────────────────────────── */
    mrs     x0, CurrentEL
    and     x0, x0, #0x0C      /* Extract EL field (bits [3:2]) */
    cmp     x0, #0x08          /* EL2? (0x08 = EL2 << 2) */
    b.eq    .drop_to_el1
    cmp     x0, #0x04          /* EL1? (0x04 = EL1 << 2) */
    b.eq    .at_el1

    /* At EL3 — configure for non-secure EL1 */
    /* (Simplified: QEMU virt typically starts at EL1 or EL2) */
    b       .at_el1

/* ── Drop from EL2 to EL1 ──────────────────────────────────────── */
.drop_to_el1:
    /* Set EL1 to be AArch64 */
    mov     x0, #(1 << 31)         /* HCR_EL2.RW = 1 (EL1 is AArch64) */
    msr     hcr_el2, x0

    /* Set up SPSR_EL2 for return to EL1h */
    mov     x0, #0x3C5             /* DAIF masked, EL1h (M[3:0]=0101) */
    msr     spsr_el2, x0

    /* Set ELR_EL2 to continue at .at_el1 */
    adr     x0, .at_el1
    msr     elr_el2, x0

    /* Return to EL1 */
    eret

/* ── At EL1: main setup ────────────────────────────────────────── */
.at_el1:
    /* Disable MMU and caches initially */
    mrs     x0, sctlr_el1
    bic     x0, x0, #(1 << 0)     /* M: MMU disable */
    bic     x0, x0, #(1 << 2)     /* C: Data cache disable */
    bic     x0, x0, #(1 << 12)    /* I: Instruction cache disable */
    msr     sctlr_el1, x0
    isb

    /* Set VBAR_EL1 — exception vector table */
    ldr     x0, =vectors
    msr     vbar_el1, x0
    isb

    /* Set up initial kernel stack */
    ldr     x0, =stack_top
    mov     sp, x0

    /* ── Zero BSS section ───────────────────────────────────────── */
    ldr     x0, =_bss_start
    ldr     x1, =_bss_end
.bss_loop:
    cmp     x0, x1
    b.ge    .bss_done
    str     xzr, [x0], #8
    b       .bss_loop
.bss_done:

    /* ── Call kernel entry point ─────────────────────────────────── */
    bl      kernel_main

    /* ── Halt loop ───────────────────────────────────────────────── */
.halt_loop:
    wfe
    b       .halt_loop

.size _start, . - _start

/* ══════════════════════════════════════════════════════════════════════
 * BSS: Stack reservation
 * ══════════════════════════════════════════════════════════════════════ */

.section .bss, "aw", @nobits
.balign 16

stack_bottom:
    .space STACK_SIZE
stack_top:
