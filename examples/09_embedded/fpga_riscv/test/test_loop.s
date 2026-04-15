# Test loop: sum 1+2+3+...+10 = 55, write to LED
# Expected: LED = 55

.section .text
.globl _start
_start:
    li   a0, 0             # sum = 0
    li   a1, 1             # i = 1
    li   a2, 11            # limit = 11
loop:
    add  a0, a0, a1        # sum += i
    addi a1, a1, 1         # i++
    blt  a1, a2, loop      # if i < 11, loop
    lui  t0, 0x80000
    sw   a0, 0(t0)         # LED = 55
    ecall
