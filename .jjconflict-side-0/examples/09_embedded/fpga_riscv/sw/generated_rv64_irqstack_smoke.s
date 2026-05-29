    .section .text
    .globl _start
_start:
    lui t0, 0x80000
    la t1, trap_handler
    csrrw zero, mtvec, t1
    addi t1, zero, 0x80
    csrrw zero, mie, t1
    addi t1, zero, 0x8
    csrrw zero, mstatus, t1
    csrrw zero, mscratch, zero

wait_loop:
    csrrs t2, mscratch, zero
    beq t2, zero, wait_loop

after_irq:
    csrrs t2, mstatus, zero
    andi t3, t2, 0x8
    addi t4, zero, 0x8
    bne t3, t4, fail_1
    andi t3, t2, 0x80
    addi t4, zero, 0x80
    bne t3, t4, fail_2

    addi t6, zero, 42
    sd t6, 256(t0)
    sd zero, 264(t0)
    ebreak

trap_handler:
    csrrs t2, mstatus, zero
    andi t3, t2, 0x8
    bne t3, zero, fail_4
    andi t3, t2, 0x80
    addi t4, zero, 0x80
    bne t3, t4, fail_5

    addi t3, zero, 1
    csrrw zero, mscratch, t3
    la t3, after_irq
    csrrw zero, mepc, t3
    mret

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
