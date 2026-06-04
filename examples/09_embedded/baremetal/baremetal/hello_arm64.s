# ARM64/AArch64 Bare-Metal Hello World
# Exception vectors, UART output

.section .vectors
.align 11  // Vector table must be 2KB aligned
.global _vectors

_vectors:
    // EL1t (Current EL with SP_EL0)
    b _start                          // Synchronous
    .align 7
    b hang                            // IRQ
    .align 7
    b hang                            // FIQ
    .align 7
    b hang                            // SError

    // EL1h (Current EL with SP_ELx)
    .align 7
    b hang                            // Synchronous
    .align 7
    b hang                            // IRQ
    .align 7
    b hang                            // FIQ
    .align 7
    b hang                            // SError

    // EL0 (Lower EL using AArch64)
    .align 7
    b hang                            // Synchronous
    .align 7
    b hang                            // IRQ
    .align 7
    b hang                            // FIQ
    .align 7
    b hang                            // SError

    // EL0 (Lower EL using AArch32)
    .align 7
    b hang                            // Synchronous
    .align 7
    b hang                            // IRQ
    .align 7
    b hang                            // FIQ
    .align 7
    b hang                            // SError

.section .text
.global _start

_start:
    // Set up stack
    ldr x0, =_stack_top
    mov sp, x0

    // Write "Hello, ARM64!" to UART (0x09000000 for virt machine)
    ldr x0, =0x09000000               // UART base
    ldr x1, =hello_msg
    mov x2, #13                       // Message length

write_loop:
    cbz x2, exit
    ldrb w3, [x1], #1                 // Load byte, increment
    strb w3, [x0]                     // Write to UART
    sub x2, x2, #1
    b write_loop

exit:
    // Exit via QEMU semihosting or just halt
    mov x0, #0x18                     // Exit code
    hlt #0xF000                       // Breakpoint

hang:
    wfi
    b hang

.section .rodata
hello_msg:
    .ascii "Hello, ARM64!"

.section .bss
.align 4
_stack_bottom:
    .space 8192
_stack_top:
