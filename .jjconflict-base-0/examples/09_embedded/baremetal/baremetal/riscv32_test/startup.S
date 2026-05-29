# RISC-V 32-bit Bare-Metal Startup
# Minimal startup code for QEMU virt machine
#
# Sets up stack and calls main()

.section .text
.global _start
.extern main

_start:
    # Set up stack pointer (top of 16KB RAM at 0x80004000)
    lui sp, %hi(0x80004000)
    addi sp, sp, %lo(0x80004000)

    # Clear BSS section
    la t0, __bss_start
    la t1, __bss_end
clear_bss:
    bge t0, t1, bss_done
    sw zero, 0(t0)
    addi t0, t0, 4
    j clear_bss
bss_done:

    # Call main
    jal ra, main

    # If main returns, exit via semihosting with its return value
    mv a1, a0               # return value = exit code
    li a0, 0x18             # SYS_EXIT
    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Fallback halt
halt:
    wfi
    j halt

# Provide weak BSS symbols in case linker doesn't define them
.weak __bss_start
.weak __bss_end
