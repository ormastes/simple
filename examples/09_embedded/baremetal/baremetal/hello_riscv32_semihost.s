# RISC-V 32-bit Bare-Metal Hello World with Semihosting
# Uses RISC-V semihosting specification for output
#
# Build:
#   riscv64-unknown-elf-as -march=rv32i -mabi=ilp32 hello_riscv32_semihost.s -o hello_riscv32_semihost.o
#   riscv64-unknown-elf-ld -m elf32lriscv hello_riscv32_semihost.o -o hello_riscv32_semihost.elf -Ttext=0x80000000
#
# Run:
#   qemu-system-riscv32 -M virt -kernel hello_riscv32_semihost.elf -nographic -semihosting-config enable=on,target=native

.section .text
.global _start

_start:
    # Set up stack (use end of RAM at 0x80004000)
    lui sp, %hi(0x80004000)
    addi sp, sp, %lo(0x80004000)

    # Print "Hello, RISC-V 32!" via semihosting SYS_WRITE0
    # SYS_WRITE0 = 0x04 (write null-terminated string)
    # a0 = operation number
    # a1 = pointer to string
    li a0, 0x04              # SYS_WRITE0
    la a1, hello_msg         # String pointer

    # RISC-V semihosting magic sequence
    .option push
    .option norvc             # Disable compressed instructions
    slli zero, zero, 0x1f    # Entry magic NOP
    ebreak                    # Trigger semihosting
    srai zero, zero, 0x7     # Exit magic NOP
    .option pop

    # Print success message
    li a0, 0x04              # SYS_WRITE0
    la a1, success_msg
    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Exit with code 0 via semihosting
    # SYS_EXIT = 0x18
    # a0 = operation number
    # a1 = exit code
    li a0, 0x18              # SYS_EXIT
    li a1, 0                 # Exit code 0

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Fallback: halt forever if semihosting not available
halt:
    wfi                      # Wait for interrupt
    j halt

.section .rodata
hello_msg:
    .asciz "Hello, RISC-V 32!\n"

success_msg:
    .asciz "[SEMIHOST TEST] Success - exit code 0\n"

.section .bss
.align 16
stack_bottom:
    .skip 8192               # 8 KB stack
stack_top:
