    .section .text
    .globl _start
_start:
    lui t0, 0x80000
    addi t1, zero, -86

    sw zero, 288(t0)
    sb t1, 288(t0)
    sb t1, 289(t0)
    sb t1, 290(t0)
    sb t1, 291(t0)
    lw t2, 288(t0)
    lui t3, 0xaaaab
    addi t3, t3, -1366
    bne t2, t3, fail_1

    lui t3, 0x11223
    addi t3, t3, 836
    sw t3, 288(t0)
    sb t1, 289(t0)
    lw t2, 288(t0)
    lui t3, 0x1122b
    addi t3, t3, -1468
    bne t2, t3, fail_2

    lui t3, 0xffffc
    addi t3, t3, -1093
    sh t3, 288(t0)
    lw t2, 288(t0)
    lui t3, 0x1122c
    addi t3, t3, -1093
    bne t2, t3, fail_3

    lui t3, 0xffffd
    addi t3, t3, -820
    sh t3, 290(t0)
    lw t2, 288(t0)
    lui t3, 0xccccc
    addi t3, t3, -1093
    bne t2, t3, fail_4

    lui t3, 0x55667
    addi t3, t3, 1928
    sw t3, 288(t0)
    lw t2, 288(t0)
    bne t2, t3, fail_5

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
