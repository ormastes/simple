    .section .text
    .globl _start
_start:
    lui t0, 0x80000

    addi t1, zero, 0x23
    csrrw t2, mscratch, t1
    bne t2, zero, fail_1

    csrrs t3, mscratch, zero
    bne t3, t1, fail_2

    addi t4, zero, 0x20
    csrrc t5, mscratch, t4
    bne t5, t1, fail_3

    addi t6, zero, 0x03
    csrrs t3, mscratch, zero
    bne t3, t6, fail_4

    csrrwi t2, mtvec, 9
    bne t2, zero, fail_5

    addi t4, zero, 9
    csrrsi t5, mtvec, 4
    bne t5, t4, fail_6

    addi t4, zero, 13
    csrrci t5, mtvec, 1
    bne t5, t4, fail_7

    addi t4, zero, 12
    csrrs t3, mtvec, zero
    bne t3, t4, fail_8

    csrrs t3, mstatus, zero
    bne t3, zero, fail_9

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
