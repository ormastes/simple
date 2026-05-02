.section .text
.globl _start

_start:
    li t6, 0x110
    sd a0, 0(t6)
    sd a1, 8(t6)

    li t2, 0x10000000
    li t3, 'L'
    sb t3, 0(t2)
    li t3, 'N'
    sb t3, 0(t2)
    li t3, 'X'
    sb t3, 0(t2)
    li t3, 'H'
    sb t3, 0(t2)

    li t4, 0x100
    li t5, 42
    sd t5, 0(t4)
    ebreak
