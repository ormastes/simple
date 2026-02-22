# RISC-V 32-bit Bare-Metal SSpec Test with Semihosting
# Outputs SSpec-compatible format for test runner parsing
#
# Build:
#   riscv64-linux-gnu-as -march=rv32i -mabi=ilp32 hello_riscv32_sspec.s -o /tmp/hello_riscv32_sspec.o
#   riscv64-linux-gnu-ld -m elf32lriscv /tmp/hello_riscv32_sspec.o -o hello_riscv32_sspec.elf -Ttext=0x80000000
#
# Run:
#   qemu-system-riscv32 -M virt -bios none -kernel hello_riscv32_sspec.elf -nographic -semihosting-config enable=on,target=native

.section .text
.global _start

_start:
    # Set up stack
    lui sp, %hi(0x80004000)
    addi sp, sp, %lo(0x80004000)

    # Print SSpec header
    li a0, 0x04
    la a1, msg_header
    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Print PASS line
    li a0, 0x04
    la a1, msg_pass
    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Print summary line (SSpec format)
    li a0, 0x04
    la a1, msg_summary
    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Exit with code 0
    li a0, 0x18
    li a1, 0
    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

halt:
    wfi
    j halt

.section .rodata
msg_header:
    .asciz "Baremetal Semihosting\n"
msg_pass:
    .asciz "  hello_semihost\n"
msg_summary:
    .asciz "\n1 examples, 0 failures\n"
