    .section .text
    .globl _start
_start:
    lui t0, 0x80000
    lui t1, 0x80ff8
    addi t1, t1, -255
    sw t1, 288(t0)

    lb t2, 291(t0)
    addi t3, zero, -128
    bne t2, t3, fail_1

    lbu t2, 291(t0)
    addi t3, zero, 128
    bne t2, t3, fail_2

    lb t2, 289(t0)
    addi t3, zero, 127
    bne t2, t3, fail_3

    lh t2, 290(t0)
    lui t3, 0xffff8
    addi t3, t3, 255
    bne t2, t3, fail_4

    lhu t2, 290(t0)
    lui t3, 0x8
    addi t3, t3, 255
    bne t2, t3, fail_5

    lw t2, 288(t0)
    bne t2, t1, fail_6

    addi t4, zero, 42
    sw t4, 256(t0)
    sw zero, 260(t0)
    ebreak

fail_1:
    addi t4, zero, 1
    sw t4, 260(t0)
    ebreak

fail_2:
    addi t4, zero, 2
    sw t4, 260(t0)
    ebreak

fail_3:
    addi t4, zero, 3
    sw t4, 260(t0)
    ebreak

fail_4:
    addi t4, zero, 4
    sw t4, 260(t0)
    ebreak

fail_5:
    addi t4, zero, 5
    sw t4, 260(t0)
    ebreak

fail_6:
    addi t4, zero, 6
    sw t4, 260(t0)
    ebreak
