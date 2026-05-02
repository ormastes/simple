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
wait_branch:
    beq t2, zero, wait_loop

after_irq:
    csrrs t2, mscratch, zero
    addi t3, zero, 1
    bne t2, t3, fail_1

    csrrs t2, mcause, zero
    blt t2, zero, cause_sign_ok
    beq zero, zero, fail_2

cause_sign_ok:
    andi t2, t2, 255
    addi t4, zero, 7
    bne t2, t4, fail_3

    ld t5, 272(t0)
    la t4, wait_loop
    beq t5, t4, mepc_ok
    la t4, wait_branch
    bne t5, t4, fail_4

mepc_ok:
    la t4, after_irq
    csrrs t5, mepc, zero
    bne t5, t4, fail_5

    addi t6, zero, 42
    sd t6, 256(t0)
    sd zero, 264(t0)
    ebreak

trap_handler:
    csrrs t2, mepc, zero
    sd t2, 272(t0)
    la t2, after_irq
    csrrw zero, mepc, t2
    addi t3, zero, 1
    csrrw zero, mscratch, t3
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
