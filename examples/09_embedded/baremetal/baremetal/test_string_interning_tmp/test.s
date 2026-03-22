.section .text
.global _start

# RISC-V semihosting call macro
.macro semihost_call
    .align 4
    slli x0, x0, 0x1f   # Entry NOP
    ebreak              # Breakpoint triggers semihosting
    srai x0, x0, 7      # Exit NOP
.endm

_start:
    # Print string ID 1: "Hello, RISC-V!\n"
    li a0, 0x100        # Syscall number: SYS_WRITE_HANDLE
    li a1, 1            # Argument: string ID
    semihost_call

    # Print string ID 2: "[TEST] String interning works!\n"
    li a0, 0x100        # Syscall number: SYS_WRITE_HANDLE
    li a1, 2            # Argument: string ID
    semihost_call

    # Exit
    li a0, 0x18         # Syscall number: SYS_EXIT
    li a1, 0            # Argument: exit code 0
    semihost_call

.align 4
