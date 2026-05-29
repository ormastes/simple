    .section .text
    .globl _start
_start:
    lui t0, 0x80000

    sd zero, 288(t0)

    addi t1, zero, 17
    sb t1, 288(t0)
    sb t1, 289(t0)
    sb t1, 290(t0)
    sb t1, 291(t0)
    lbu t2, 288(t0)
    bne t2, t1, fail_1
    lbu t2, 289(t0)
    bne t2, t1, fail_1
    lbu t2, 290(t0)
    bne t2, t1, fail_1
    lbu t2, 291(t0)
    bne t2, t1, fail_1

    lui t3, 0x11223
    addi t3, t3, 836
    sw t3, 288(t0)
    addi t1, zero, 34
    sb t1, 289(t0)
    lbu t2, 288(t0)
    addi t4, zero, 68
    bne t2, t4, fail_2
    lbu t2, 289(t0)
    bne t2, t1, fail_2
    lbu t2, 290(t0)
    addi t4, zero, 34
    bne t2, t4, fail_2
    lbu t2, 291(t0)
    addi t4, zero, 17
    bne t2, t4, fail_2

    lui t3, 0x2
    addi t3, t3, 819
    sh t3, 292(t0)
    lhu t2, 292(t0)
    bne t2, t3, fail_3

    lui t3, 0x44556
    addi t3, t3, 1655
    sw t3, 296(t0)
    lwu t2, 296(t0)
    bne t2, t3, fail_4

    addi t3, zero, 42
    sd t3, 256(t0)
    sd zero, 264(t0)
    ebreak

fail_1:
    addi t4, zero, 1
    sd t4, 264(t0)
    ebreak

fail_2:
    addi t4, zero, 2
    sd t4, 264(t0)
    ebreak

fail_3:
    addi t4, zero, 3
    sd t4, 264(t0)
    ebreak

fail_4:
    addi t4, zero, 4
    sd t4, 264(t0)
    ebreak
