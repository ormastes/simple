/*
 * startup.S — Boot entry point for ARM32 (QEMU virt, Cortex-A15)
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Entry point for the kernel. Sets up stacks for each processor mode,
 * installs the vector table, zeros BSS, and calls kernel_main().
 *
 * QEMU loads the binary at 0x40000000 (RAM base for -M virt).
 */

/* ── Stack sizes ──────────────────────────────────────────────────── */

.set SVC_STACK_SIZE,    16384       /* 16 KB — main kernel stack     */
.set IRQ_STACK_SIZE,    4096        /* 4 KB                          */
.set ABT_STACK_SIZE,    4096        /* 4 KB                          */
.set UND_STACK_SIZE,    4096        /* 4 KB                          */
.set FIQ_STACK_SIZE,    4096        /* 4 KB                          */

/* ── ARM processor modes ──────────────────────────────────────────── */

.set MODE_SVC,  0x13
.set MODE_IRQ,  0x12
.set MODE_FIQ,  0x11
.set MODE_ABT,  0x17
.set MODE_UND,  0x1B
.set MODE_SYS,  0x1F
.set I_BIT,     0x80        /* IRQ disable */
.set F_BIT,     0x40        /* FIQ disable */

/* ══════════════════════════════════════════════════════════════════════
 * Entry point
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global _start
.type _start, %function

_start:
    /* Ensure we are in SVC mode with IRQs/FIQs disabled */
    cps     #MODE_SVC
    cpsid   if

    /* ── Install vector table via VBAR ── */
    ldr     r0, =vector_table
    mcr     p15, 0, r0, c12, c0, 0     /* Write VBAR */
    isb

    /* ── Set up mode stacks ── */
    /* Use msr cpsr_c to set mode + disable IRQ/FIQ simultaneously */

    /* IRQ mode stack */
    msr     cpsr_c, #(MODE_IRQ | I_BIT | F_BIT)
    ldr     sp, =irq_stack_top

    /* ABT mode stack */
    msr     cpsr_c, #(MODE_ABT | I_BIT | F_BIT)
    ldr     sp, =abt_stack_top

    /* UND mode stack */
    msr     cpsr_c, #(MODE_UND | I_BIT | F_BIT)
    ldr     sp, =und_stack_top

    /* FIQ mode stack */
    msr     cpsr_c, #(MODE_FIQ | I_BIT | F_BIT)
    ldr     sp, =fiq_stack_top

    /* Back to SVC mode for kernel execution */
    msr     cpsr_c, #(MODE_SVC | I_BIT | F_BIT)
    ldr     sp, =svc_stack_top

    /* ── Zero BSS ── */
    ldr     r0, =_bss_start
    ldr     r1, =_bss_end
    mov     r2, #0
.bss_loop:
    cmp     r0, r1
    strlt   r2, [r0], #4
    blt     .bss_loop

    /* ── Enable IRQs ── */
    cpsie   i

    /* ── Call kernel_main() ── */
    bl      kernel_main

    /* ── If kernel_main returns, halt ── */
.halt_loop:
    cpsid   if
    wfi
    b       .halt_loop

.size _start, . - _start

/* ══════════════════════════════════════════════════════════════════════
 * BSS: Stack reservations for each mode
 * ══════════════════════════════════════════════════════════════════════ */

.section .bss, "aw", %nobits
.align 4

svc_stack_bottom:
    .space SVC_STACK_SIZE
svc_stack_top:

irq_stack_bottom:
    .space IRQ_STACK_SIZE
irq_stack_top:

abt_stack_bottom:
    .space ABT_STACK_SIZE
abt_stack_top:

und_stack_bottom:
    .space UND_STACK_SIZE
und_stack_top:

fiq_stack_bottom:
    .space FIQ_STACK_SIZE
fiq_stack_top:
