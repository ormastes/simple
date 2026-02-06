# Minimal RISC-V 32-bit test program for remote debugger testing.
# Runs on QEMU virt machine.
#
# Build: riscv32-unknown-elf-gcc -nostdlib -march=rv32imac -mabi=ilp32 -o hello_rv32.elf hello_rv32.s
# Run:   qemu-system-riscv32 -machine virt -nographic -kernel hello_rv32.elf -S -gdb tcp::1234

    .section .text
    .globl _start

_start:
    # Set up stack pointer (QEMU virt RAM starts at 0x80000000)
    li sp, 0x80100000       # Stack at RAM + 1MB

    # Call our test function
    jal ra, test_func

    # Exit via ecall (QEMU semihosting or infinite loop)
    li a0, 0                # exit code 0
    li a7, 93               # ecall: exit
    ecall

    # Fallback infinite loop if ecall doesn't work
halt:
    j halt

# Test function with local variables (useful for debugger testing)
test_func:
    addi sp, sp, -16        # Allocate stack frame
    sw ra, 12(sp)           # Save return address
    sw s0, 8(sp)            # Save frame pointer
    addi s0, sp, 16         # Set frame pointer

    # Local variables for debugger to inspect
    li a0, 42               # x = 42
    sw a0, -12(s0)          # Store x on stack

    li a1, 58               # y = 58
    sw a1, -16(s0)          # Store y on stack

    add a2, a0, a1          # z = x + y = 100

    # Restore and return
    lw ra, 12(sp)
    lw s0, 8(sp)
    addi sp, sp, 16
    ret
