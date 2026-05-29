# RISC-V 64-bit Bare-Metal Hello World
# Machine mode boot, UART output

.section .text
.global _start

_start:
    # Set up stack
    la sp, _stack_top

    # Write "Hello, RISC-V 64!" to UART (0x10000000)
    li a0, 0x10000000                 # UART base
    la a1, hello_msg
    li a2, 17                         # Message length

write_loop:
    beqz a2, exit
    lbu a3, 0(a1)                     # Load byte
    sb a3, 0(a0)                      # Write to UART
    addi a1, a1, 1
    addi a2, a2, -1
    j write_loop

exit:
    # Exit via SiFive test device
    li a0, 0x100000
    li a1, 0x5555
    sw a1, 0(a0)

halt:
    wfi
    j halt

.section .rodata
hello_msg:
    .ascii "Hello, RISC-V 64!"

.section .bss
.align 4
_stack_bottom:
    .space 8192
_stack_top:
