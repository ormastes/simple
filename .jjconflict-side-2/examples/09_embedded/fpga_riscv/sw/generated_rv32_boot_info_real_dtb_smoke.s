.section .text
.globl _start

_start:
    mv s0, a0
    mv s1, a1

    li t6, 0x80000110
    sw s0, 0(t6)
    sw s1, 4(t6)

    lbu t0, 0(s1)
    li t1, 0xD0
    bne t0, t1, fail
    lbu t0, 1(s1)
    li t1, 0x0D
    bne t0, t1, fail
    lbu t0, 2(s1)
    li t1, 0xFE
    bne t0, t1, fail
    lbu t0, 3(s1)
    li t1, 0xED
    bne t0, t1, fail

    li t2, 1
    li t3, 0x80000118
    sw t2, 0(t3)

    li t2, 0x10000000
    li t4, 'R'
    sb t4, 0(t2)
    li t4, 'D'
    sb t4, 0(t2)
    li t4, 'T'
    sb t4, 0(t2)
    li t4, 'B'
    sb t4, 0(t2)

    li t5, 0x80000100
    li t4, 42
    sw t4, 0(t5)
    ebreak

fail:
    li t2, 0x10000000
    li t4, 'F'
    sb t4, 0(t2)
    li t4, 'A'
    sb t4, 0(t2)
    li t4, 'I'
    sb t4, 0(t2)
    li t4, 'L'
    sb t4, 0(t2)
    ebreak
