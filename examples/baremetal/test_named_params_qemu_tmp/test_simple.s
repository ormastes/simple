.section .text
.global _start

.macro semihost_call
    .align 4
    slli x0, x0, 0x1f
    ebreak
    srai x0, x0, 7
.endm

_start:
    # Test just ID 1 with parameter
    li a0, 0x101        # SYS_WRITE_HANDLE_P1
    li a1, 1            # String ID 1
    li a2, 42           # Parameter value
    semihost_call

    # Exit
    li a0, 0x18
    li a1, 0
    semihost_call
