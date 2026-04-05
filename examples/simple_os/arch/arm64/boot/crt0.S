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
