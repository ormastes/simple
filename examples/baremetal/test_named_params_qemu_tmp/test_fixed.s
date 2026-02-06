.section .data
.align 4
# Parameter blocks in memory (RISC-V semihosting requires this)
params_1:
    .word 42              # name = 42

params_2:
    .word 100             # username = 100
    .word 25              # age = 25

params_3:
    .word 255             # r = 255
    .word 128             # g = 128
    .word 64              # b = 64

.section .text
.global _start

.macro semihost_call
    .align 4
    slli x0, x0, 0x1f
    ebreak
    srai x0, x0, 7
.endm

_start:
    # Test 1: Single parameter {name}
    li a0, 0x101                # SYS_WRITE_HANDLE_P1
    la a1, params_1             # Pointer to parameters in memory
    semihost_call

    # Test 2: Two parameters {username}, {age}
    li a0, 0x102                # SYS_WRITE_HANDLE_P2
    la a1, params_2             # Pointer to parameters
    semihost_call

    # Test 3: Three parameters {r}, {g}, {b}
    li a0, 0x103                # SYS_WRITE_HANDLE_P3
    la a1, params_3             # Pointer to parameters
    semihost_call

    # Exit
    li a0, 0x18
    li a1, 0
    semihost_call
