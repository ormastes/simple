    .section .text
    .globl _start
_start:
    lui t0, 0x80000

    addi t1, zero, -128
    sb t1, 320(t0)
    lb t2, 320(t0)
    bne t2, t1, fail_1
    lbu t2, 320(t0)
    addi t3, zero, 128
    bne t2, t3, fail_2

    lui t1, 0x10
    addi t1, t1, -128
    sh t1, 322(t0)
    lh t2, 322(t0)
    addi t3, zero, -128
    bne t2, t3, fail_3
    lhu t2, 322(t0)
    bne t2, t1, fail_4

    addi t1, zero, -128
    sw t1, 328(t0)
    lw t2, 328(t0)
    bne t2, t1, fail_5
    lwu t2, 328(t0)
    beq t2, t1, fail_6_hi
    slt t3, t2, zero
    bne t3, zero, fail_6_lo

    lui t1, 0x12345
    addi t1, t1, 1656
    sd t1, 336(t0)
    ld t2, 336(t0)
    bne t2, t1, fail_7

    addi t4, zero, 42
    sd t4, 256(t0)
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

fail_5:
    addi t4, zero, 5
    sd t4, 264(t0)
    ebreak

fail_6_hi:
    addi t4, zero, 6
    sd t4, 264(t0)
    ebreak

fail_6_lo:
    addi t4, zero, 7
    sd t4, 264(t0)
    ebreak

fail_7:
    addi t4, zero, 8
    sd t4, 264(t0)
    ebreak
