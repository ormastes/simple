/*
 * isr_stubs.S — 64-bit ISR / IRQ stub assembly for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Provides low-level entry points for all 32 CPU exceptions and
 * 16 hardware IRQs. Each stub pushes a uniform stack frame and
 * calls the C trap_handler().
 *
 * In 64-bit mode:
 *   - pusha/popa do not exist; we push individual registers
 *   - Stack must be 16-byte aligned before call
 *   - iretq instead of iret
 */

/* ══════════════════════════════════════════════════════════════════════
 * Macros for ISR stubs
 * ══════════════════════════════════════════════════════════════════════ */

/*
 * ISR_NOERR — exception that does NOT push an error code.
 * We push a dummy zero so the stack frame is uniform.
 */
.macro ISR_NOERR num
    .global isr\num
    .type   isr\num, @function
    isr\num:
        pushq   $0              /* dummy error code */
        pushq   $\num           /* interrupt number  */
        jmp     isr_common
.endm

/*
 * ISR_ERR — exception that pushes its own error code.
 */
.macro ISR_ERR num
    .global isr\num
    .type   isr\num, @function
    isr\num:
        /* error code already on stack from CPU */
        pushq   $\num           /* interrupt number  */
        jmp     isr_common
.endm

/*
 * IRQ_STUB — hardware IRQ remapped to vector (irq_num + 32).
 */
.macro IRQ_STUB irq_num vec_num
    .global irq\irq_num
    .type   irq\irq_num, @function
    irq\irq_num:
        pushq   $0              /* dummy error code */
        pushq   $\vec_num       /* vector number    */
        jmp     isr_common
.endm

/* ══════════════════════════════════════════════════════════════════════
 * CPU exceptions 0..31
 * Exceptions 8, 10, 11, 12, 13, 14, 17, 21, 29, 30 push error codes.
 * ══════════════════════════════════════════════════════════════════════ */

ISR_NOERR  0        /* #DE  Divide Error                */
ISR_NOERR  1        /* #DB  Debug                       */
ISR_NOERR  2        /*      NMI                         */
ISR_NOERR  3        /* #BP  Breakpoint                  */
ISR_NOERR  4        /* #OF  Overflow                    */
ISR_NOERR  5        /* #BR  Bound Range Exceeded        */
ISR_NOERR  6        /* #UD  Invalid Opcode              */
ISR_NOERR  7        /* #NM  Device Not Available        */
ISR_ERR    8        /* #DF  Double Fault                */
ISR_NOERR  9        /*      Coprocessor Segment Overrun */
ISR_ERR   10        /* #TS  Invalid TSS                 */
ISR_ERR   11        /* #NP  Segment Not Present         */
ISR_ERR   12        /* #SS  Stack-Segment Fault         */
ISR_ERR   13        /* #GP  General Protection Fault    */
ISR_ERR   14        /* #PF  Page Fault                  */
ISR_NOERR 15        /*      Reserved                    */
ISR_NOERR 16        /* #MF  x87 FPU Error               */
ISR_ERR   17        /* #AC  Alignment Check             */
ISR_NOERR 18        /* #MC  Machine Check               */
ISR_NOERR 19        /* #XM  SIMD FP Exception           */
ISR_NOERR 20        /* #VE  Virtualisation Exception    */
ISR_ERR   21        /* #CP  Control Protection          */
ISR_NOERR 22        /*      Reserved                    */
ISR_NOERR 23        /*      Reserved                    */
ISR_NOERR 24        /*      Reserved                    */
ISR_NOERR 25        /*      Reserved                    */
ISR_NOERR 26        /*      Reserved                    */
ISR_NOERR 27        /*      Reserved                    */
ISR_NOERR 28        /*      Reserved                    */
ISR_ERR   29        /* #SX  Security Exception          */
ISR_ERR   30        /* #HV  Hypervisor Injection        */
ISR_NOERR 31        /*      Reserved                    */

/* ══════════════════════════════════════════════════════════════════════
 * Hardware IRQs 0..15  (mapped to vectors 32..47)
 * ══════════════════════════════════════════════════════════════════════ */

IRQ_STUB  0, 32     /* PIT / Timer                      */
IRQ_STUB  1, 33     /* Keyboard                         */
IRQ_STUB  2, 34     /* Cascade (PIC2)                   */
IRQ_STUB  3, 35     /* COM2                             */
IRQ_STUB  4, 36     /* COM1                             */
IRQ_STUB  5, 37     /* LPT2                             */
IRQ_STUB  6, 38     /* Floppy                           */
IRQ_STUB  7, 39     /* LPT1 / Spurious                  */
IRQ_STUB  8, 40     /* RTC                              */
IRQ_STUB  9, 41     /* Free / ACPI                      */
IRQ_STUB 10, 42     /* Free                             */
IRQ_STUB 11, 43     /* Free                             */
IRQ_STUB 12, 44     /* PS/2 Mouse                       */
IRQ_STUB 13, 45     /* FPU / Coprocessor                */
IRQ_STUB 14, 46     /* Primary ATA                      */
IRQ_STUB 15, 47     /* Secondary ATA                    */

/* ══════════════════════════════════════════════════════════════════════
 * Common ISR handler: build trap_frame_t, call C handler, return
 *
 * Stack on entry (from CPU + our push):
 *   [rsp+8]  = int_no
 *   [rsp+0]  = err_code    (or dummy 0)
 *   ... CPU-pushed: RIP, CS, RFLAGS, RSP, SS
 *
 * We save all 64-bit GPRs individually (no pusha in long mode).
 * ══════════════════════════════════════════════════════════════════════ */

.extern trap_handler

isr_common:
    /* Save all general-purpose registers */
    pushq   %rax
    pushq   %rbx
    pushq   %rcx
    pushq   %rdx
    pushq   %rsi
    pushq   %rdi
    pushq   %rbp
    pushq   %r8
    pushq   %r9
    pushq   %r10
    pushq   %r11
    pushq   %r12
    pushq   %r13
    pushq   %r14
    pushq   %r15

    /* Load kernel data segment */
    movw    $0x10, %ax
    movw    %ax, %ds
    movw    %ax, %es

    /* Call C handler: first argument = pointer to trap frame (RSP) */
    movq    %rsp, %rdi
    call    trap_handler

    /* Restore general-purpose registers */
    popq    %r15
    popq    %r14
    popq    %r13
    popq    %r12
    popq    %r11
    popq    %r10
    popq    %r9
    popq    %r8
    popq    %rbp
    popq    %rdi
    popq    %rsi
    popq    %rdx
    popq    %rcx
    popq    %rbx
    popq    %rax

    /* Remove int_no and err_code from stack */
    addq    $16, %rsp

    /* Return from interrupt (64-bit) */
    iretq

/* ══════════════════════════════════════════════════════════════════════
 * ISR table in .rodata — array of 256 handler addresses (64-bit)
 * ══════════════════════════════════════════════════════════════════════ */

.section .rodata
.global isr_table
.type   isr_table, @object

isr_table:
    /* Exceptions 0..31 */
    .quad isr0,  isr1,  isr2,  isr3,  isr4,  isr5,  isr6,  isr7
    .quad isr8,  isr9,  isr10, isr11, isr12, isr13, isr14, isr15
    .quad isr16, isr17, isr18, isr19, isr20, isr21, isr22, isr23
    .quad isr24, isr25, isr26, isr27, isr28, isr29, isr30, isr31

    /* IRQs 32..47 */
    .quad irq0,  irq1,  irq2,  irq3,  irq4,  irq5,  irq6,  irq7
    .quad irq8,  irq9,  irq10, irq11, irq12, irq13, irq14, irq15

    /* Vectors 48..255: zero (unused) */
    .fill 208, 8, 0

.size isr_table, . - isr_table
