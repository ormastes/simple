# RISC-V 32-bit Bare-Metal Hello World
# Minimal machine mode boot, UART output, clean exit

.section .text
.global _start

_start:
    # Set up stack (use end of RAM at 0x80004000)
    lui sp, %hi(0x80004000)
    addi sp, sp, %lo(0x80004000)

    # Write "Hello, RISC-V 32!" to UART (0x10000000)
    lui a0, %hi(uart_base)
    addi a0, a0, %lo(uart_base)
    lui a1, %hi(hello_msg)
    addi a1, a1, %lo(hello_msg)
    li a2, 17                    # Message length

write_loop:
    beqz a2, exit                # If length == 0, exit
    lbu a3, 0(a1)                # Load byte from message
    sb a3, 0(a0)                 # Store to UART
    addi a1, a1, 1               # Next char
    addi a2, a2, -1              # Decrement count
    j write_loop

exit:
    # Exit via SiFive test device (QEMU)
    # Write 0x5555 to 0x100000 to signal success
    lui a0, 0x100
    li a1, 0x5555
    sw a1, 0(a0)

    # Halt forever
halt:
    wfi
    j halt

.section .rodata
hello_msg:
    .ascii "Hello, RISC-V 32!"

uart_base:
    .word 0x10000000
