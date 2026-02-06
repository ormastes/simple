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
    # Test 1: Single parameter {name}
    # Simulating: name = "Alice" (but we can't pass strings yet, so use number)
    li a0, 0x101        # SYS_WRITE_HANDLE_P1 (1 param)
    li a1, 1            # String ID
    li a2, 42           # Parameter value (simulating name)
    semihost_call

    # Test 2: Two parameters {username}, {age}
    li a0, 0x102        # SYS_WRITE_HANDLE_P2 (2 params)
    li a1, 2            # String ID
    li a2, 100          # username value
    li a3, 25           # age value
    semihost_call

    # Test 3: Three parameters {r}, {g}, {b}
    li a0, 0x103        # SYS_WRITE_HANDLE_P3 (3 params)
    li a1, 3            # String ID
    li a2, 255          # r value
    li a3, 128          # g value
    li a4, 64           # b value
    semihost_call

    # Exit
    li a0, 0x18         # SYS_EXIT
    li a1, 0            # exit code
    semihost_call

.align 4
