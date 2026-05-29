# Simple test: compute 3 + 5, write result to LED register (0x80000000)
# Expected: LEDs = 8

.section .text
.globl _start
_start:
    li   a0, 3            # a0 = 3
    li   a1, 5            # a1 = 5
    add  a2, a0, a1       # a2 = 8
    lui  t0, 0x80000      # t0 = 0x80000000 (LED base)
    sw   a2, 0(t0)        # LED = 8
    ecall                  # halt
