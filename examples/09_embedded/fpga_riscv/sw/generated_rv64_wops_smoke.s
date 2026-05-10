    .section .text
    .globl _start
_start:
    lui t0, 0x80000

    addi t1, zero, 5
    addi t2, zero, 7
    addw t3, t1, t2
    addi t4, zero, 12
    bne t3, t4, fail_1

    subw t3, t2, t1
    addi t4, zero, 2
    bne t3, t4, fail_2

    addiw t3, t1, -8
    addi t4, zero, -3
    bne t3, t4, fail_3

    addi t1, zero, 1
    slliw t3, t1, 5
    addi t4, zero, 32
    bne t3, t4, fail_4

    srliw t3, t3, 4
    addi t4, zero, 2
    bne t3, t4, fail_5

    addi t1, zero, -16
    sraiw t3, t1, 2
    addi t4, zero, -4
    bne t3, t4, fail_6

    addi t1, zero, 3
    addi t2, zero, 4
    sllw t3, t1, t2
    addi t4, zero, 48
    bne t3, t4, fail_7

    srlw t3, t3, t1
    addi t4, zero, 6
    bne t3, t4, fail_8

    addi t1, zero, -32
    addi t2, zero, 3
    sraw t3, t1, t2
    addi t4, zero, -4
    bne t3, t4, fail_9

    lui t1, 0x80000
    addi t1, t1, -1
    addiw t3, t1, 1
    slt t4, t3, zero
    addi t5, zero, 1
    bne t4, t5, fail_10

    addi t6, zero, 42
    sd t6, 256(t0)
    sd zero, 264(t0)
    ebreak

fail_1:
    addi t6, zero, 1
    sd t6, 264(t0)
    ebreak

fail_2:
    addi t6, zero, 2
    sd t6, 264(t0)
    ebreak

fail_3:
    addi t6, zero, 3
    sd t6, 264(t0)
    ebreak

fail_4:
    addi t6, zero, 4
    sd t6, 264(t0)
    ebreak

fail_5:
    addi t6, zero, 5
    sd t6, 264(t0)
    ebreak

fail_6:
    addi t6, zero, 6
    sd t6, 264(t0)
    ebreak

fail_7:
    addi t6, zero, 7
    sd t6, 264(t0)
    ebreak

fail_8:
    addi t6, zero, 8
    sd t6, 264(t0)
    ebreak

fail_9:
    addi t6, zero, 9
    sd t6, 264(t0)
    ebreak

fail_10:
    addi t6, zero, 10
    sd t6, 264(t0)
    ebreak
