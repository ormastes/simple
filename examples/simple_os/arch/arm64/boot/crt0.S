/*
 * crt0.S -- ARM64 (AArch64) startup for QEMU virt
 *
 * Sets up stack, zeroes BSS, installs exception vector table,
 * then calls _start in C (baremetal_stubs.c) which initializes
 * PL011 UART and calls spl_start (Simple entry point).
 *
 * Runs at EL1 (or EL2 if QEMU drops us there — we don't switch).
 */

    .section .text.entry, "ax", %progbits
    .globl _start
    .type _start, @function

_start:
    /* Check current EL — if EL2, drop to EL1 */
    mrs     x0, CurrentEL
    lsr     x0, x0, #2
    cmp     x0, #2
    b.ne    .Lel1_setup

    /* --- Running at EL2: configure EL1 and drop down --- */
    /* HCR_EL2: RW=1 (AArch64 at EL1), no traps */
    mov     x0, #(1 << 31)     /* RW bit */
    msr     hcr_el2, x0

    /* SCTLR_EL1: disable MMU, caches, alignment check */
    mov     x0, #0
    msr     sctlr_el1, x0

    /* Set SPSR_EL2: return to EL1h (EL1 with SP_EL1) */
    mov     x0, #5              /* M[3:0]=0b0101 = EL1h */
    msr     spsr_el2, x0

    /* Set ELR_EL2 to continue at .Lel1_setup */
    adr     x0, .Lel1_setup
    msr     elr_el2, x0
    eret

.Lel1_setup:
    /* Disable MMU, caches, and alignment check in SCTLR_EL1 */
    mrs     x0, sctlr_el1
    bic     x0, x0, #(1 << 0)  /* Clear M bit (MMU off) */
    bic     x0, x0, #(1 << 1)  /* Clear A bit (alignment check off) */
    bic     x0, x0, #(1 << 2)  /* Clear C bit (data cache off) */
    bic     x0, x0, #(1 << 12) /* Clear I bit (instruction cache off) */
    msr     sctlr_el1, x0
    isb

    /* Set up stack pointer from linker symbol */
    adrp    x0, _stack_top
    add     sp, x0, :lo12:_stack_top

    /* Zero BSS section */
    adrp    x0, _sbss
    add     x0, x0, :lo12:_sbss
    adrp    x1, _ebss
    add     x1, x1, :lo12:_ebss
.Lbss_loop:
    cmp     x0, x1
    b.ge    .Lbss_done
    str     xzr, [x0], #8
    b       .Lbss_loop
.Lbss_done:

    /* Install exception vector table */
    adrp    x0, _vectors
    add     x0, x0, :lo12:_vectors
    msr     vbar_el1, x0
    isb

    /* Call C _start (PL011 init + spl_start) */
    bl      _c_start

    /* Halt: infinite WFE loop */
.Lhalt:
    wfe
    b       .Lhalt

    .size _start, . - _start

/* ===================================================================
 * Exception Vector Table — 16 entries, 128 bytes each, 2KB aligned
 *
 * On any exception, prints "FAULT @ <ELR_EL1>" to PL011 serial
 * then halts with WFE loop.
 * =================================================================== */

    .section .text.vectors, "ax", %progbits
    .balign 2048
    .globl _vectors
_vectors:
    /* Current EL with SP0 — Synchronous */
    b       _fault_handler
    .balign 128
    /* Current EL with SP0 — IRQ */
    b       _fault_handler
    .balign 128
    /* Current EL with SP0 — FIQ */
    b       _fault_handler
    .balign 128
    /* Current EL with SP0 — SError */
    b       _fault_handler
    .balign 128

    /* Current EL with SPx — Synchronous */
    b       _fault_handler
    .balign 128
    /* Current EL with SPx — IRQ */
    b       _fault_handler
    .balign 128
    /* Current EL with SPx — FIQ */
    b       _fault_handler
    .balign 128
    /* Current EL with SPx — SError */
    b       _fault_handler
    .balign 128

    /* Lower EL using AArch64 — Synchronous */
    b       _fault_handler
    .balign 128
    /* Lower EL using AArch64 — IRQ */
    b       _fault_handler
    .balign 128
    /* Lower EL using AArch64 — FIQ */
    b       _fault_handler
    .balign 128
    /* Lower EL using AArch64 — SError */
    b       _fault_handler
    .balign 128

    /* Lower EL using AArch32 — Synchronous */
    b       _fault_handler
    .balign 128
    /* Lower EL using AArch32 — IRQ */
    b       _fault_handler
    .balign 128
    /* Lower EL using AArch32 — FIQ */
    b       _fault_handler
    .balign 128
    /* Lower EL using AArch32 — SError */
    b       _fault_handler

/* ===================================================================
 * Fault handler — prints "FAULT @ 0x<ELR_EL1>" to PL011 then halts
 * =================================================================== */

_fault_handler:
    /* Print "FAULT @ 0x" */
    ldr     x1, =0x09000000
    mov     w0, #'F'
    str     w0, [x1]
    mov     w0, #'A'
    str     w0, [x1]
    mov     w0, #'U'
    str     w0, [x1]
    mov     w0, #'L'
    str     w0, [x1]
    mov     w0, #'T'
    str     w0, [x1]
    mov     w0, #' '
    str     w0, [x1]
    mov     w0, #'@'
    str     w0, [x1]
    mov     w0, #' '
    str     w0, [x1]
    mov     w0, #'0'
    str     w0, [x1]
    mov     w0, #'x'
    str     w0, [x1]

    /* Print ELR_EL1 as 16-digit hex */
    mrs     x2, elr_el1
    mov     x3, #60
.Lhex_loop:
    lsr     x4, x2, x3
    and     x4, x4, #0xF
    cmp     x4, #10
    b.lt    .Lhex_digit
    add     w4, w4, #('a' - 10)
    b       .Lhex_emit
.Lhex_digit:
    add     w4, w4, #'0'
.Lhex_emit:
    str     w4, [x1]
    subs    x3, x3, #4
    b.ge    .Lhex_loop

    /* Print CR+LF */
    mov     w0, #'\r'
    str     w0, [x1]
    mov     w0, #'\n'
    str     w0, [x1]

    /* Also print ESR_EL1 for diagnostics */
    mov     w0, #'E'
    str     w0, [x1]
    mov     w0, #'S'
    str     w0, [x1]
    mov     w0, #'R'
    str     w0, [x1]
    mov     w0, #'='
    str     w0, [x1]
    mov     w0, #'0'
    str     w0, [x1]
    mov     w0, #'x'
    str     w0, [x1]

    mrs     x2, esr_el1
    mov     x3, #28
.Lesr_loop:
    lsr     x4, x2, x3
    and     x4, x4, #0xF
    cmp     x4, #10
    b.lt    .Lesr_digit
    add     w4, w4, #('a' - 10)
    b       .Lesr_emit
.Lesr_digit:
    add     w4, w4, #'0'
.Lesr_emit:
    str     w4, [x1]
    subs    x3, x3, #4
    b.ge    .Lesr_loop

    mov     w0, #'\r'
    str     w0, [x1]
    mov     w0, #'\n'
    str     w0, [x1]

.Lfault_halt:
    wfe
    b       .Lfault_halt
