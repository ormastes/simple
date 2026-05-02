    .section .text
    .globl _start
_start:
    lui t0, 0x80000

    addi t1, zero, -1
    csrrw zero, mstatus, t1
    csrrs t2, sstatus, zero
    andi t3, t2, 0x122
    addi t4, zero, 0x122
    bne t3, t4, fail_1
    andi t3, t2, 0x8
    bne t3, zero, fail_1

    addi t1, zero, 0x80
    csrrw zero, mideleg, t1
    csrrw zero, mie, zero
    csrrw zero, sie, t1
    csrrs t2, sie, zero
    bne t2, t1, fail_2
    csrrs t2, mie, zero
    bne t2, t1, fail_3
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
