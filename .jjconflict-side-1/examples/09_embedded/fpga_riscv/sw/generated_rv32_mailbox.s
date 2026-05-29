    .section .text
    .globl _start
_start:
    lui t0, 0x80ff0
    addi s0, zero, 1
    addi s1, zero, 2
    li s2, 0xdead

    sw s0, 0(t0)
    addi a0, zero, 79
    sw a0, 4(t0)
    sw s0, 20(t0)
    sw s2, 24(t0)

    sw s0, 0(t0)
    addi a0, zero, 75
    sw a0, 4(t0)
    sw s0, 20(t0)
    sw s2, 24(t0)

    sw s0, 0(t0)
    addi a0, zero, 10
    sw a0, 4(t0)
    sw s0, 20(t0)
    sw s2, 24(t0)

    addi a0, zero, 3
    sw a0, 0(t0)
    sw s0, 4(t0)
    addi a1, zero, 42
    sw a1, 8(t0)
    sw s0, 20(t0)
    sw s2, 24(t0)

    sw s1, 0(t0)
    sw zero, 4(t0)
    sw s1, 20(t0)
    sw s2, 24(t0)

hang:
    j hang
