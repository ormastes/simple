.section .data
.align 4
params_1:
    .word 1               # String ID
    .word 42              # Parameter: name

params_2:
    .word 2               # String ID
    .word 100             # Parameter: username
    .word 25              # Parameter: age

params_3:
    .word 3               # String ID
    .word 255             # Parameter: r
    .word 128             # Parameter: g
    .word 64              # Parameter: b

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
    li a0, 0x101                # SYS_WRITE_HANDLE_P1
    la a1, params_1
    semihost_call

    # Test 2: Two parameters {username}, {age}
    li a0, 0x102                # SYS_WRITE_HANDLE_P2
    la a1, params_2
    semihost_call

    # Test 3: Three parameters {r}, {g}, {b}
    li a0, 0x103                # SYS_WRITE_HANDLE_P3
    la a1, params_3
    semihost_call

    # Exit
    li a0, 0x18         # SYS_EXIT
    li a1, 0            # exit code
    semihost_call

.align 4
