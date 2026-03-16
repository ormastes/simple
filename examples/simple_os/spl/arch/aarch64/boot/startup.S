/*
 * startup.S — AArch64 boot entry point
 *
 * Part of the SimpleOS L4 microkernel (Simple language build).
 *
 * Boot sequence:
 *   1. Check current EL, drop from EL2 to EL1 if needed
 *   2. Set VBAR_EL1 (exception vector base)
 *   3. Set up initial kernel stack
 *   4. Zero BSS
 *   5. Call kernel_main
 *   6. WFE loop if kernel_main returns
 */

.set STACK_SIZE, 16384

.section .text.boot
.global _start
.type _start, @function

_start:
    /* Check current exception level */
    mrs     x0, CurrentEL
    and     x0, x0, #0x0C
    cmp     x0, #0x08          /* EL2? */
    b.eq    .drop_to_el1
    cmp     x0, #0x04          /* EL1? */
    b.eq    .at_el1
    b       .at_el1

.drop_to_el1:
    /* Set EL1 to AArch64 */
    mov     x0, #(1 << 31)     /* HCR_EL2.RW = 1 */
    msr     hcr_el2, x0

    /* SPSR_EL2: DAIF masked, return to EL1h */
    mov     x0, #0x3C5
    msr     spsr_el2, x0

    /* ELR_EL2: continue at .at_el1 */
    adr     x0, .at_el1
    msr     elr_el2, x0
    eret

.at_el1:
    /* Disable MMU and caches initially */
    mrs     x0, sctlr_el1
    bic     x0, x0, #(1 << 0)     /* M: MMU off */
    bic     x0, x0, #(1 << 2)     /* C: D-cache off */
    bic     x0, x0, #(1 << 12)    /* I: I-cache off */
    msr     sctlr_el1, x0
    isb

    /* Set VBAR_EL1 */
    ldr     x0, =vectors
    msr     vbar_el1, x0
    isb

    /* Set up kernel stack */
    ldr     x0, =stack_top
    mov     sp, x0

    /* Zero BSS */
    ldr     x0, =_bss_start
    ldr     x1, =_bss_end
.bss_loop:
    cmp     x0, x1
    b.ge    .bss_done
    str     xzr, [x0], #8
    b       .bss_loop
.bss_done:

    /* Call kernel entry */
    bl      kernel_main

.halt_loop:
    wfe
    b       .halt_loop

.size _start, . - _start

/* Stack reservation */
.section .bss, "aw", @nobits
.balign 16
stack_bottom:
    .space STACK_SIZE
stack_top:
