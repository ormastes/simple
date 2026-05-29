    .section .text
    .globl _start
_start:
    lui t0, 0x80000
    la t1, s_handler
    csrrw zero, stvec, t1
    addi t1, zero, 0x20
    csrrw zero, mideleg, t1
    csrrs t2, mideleg, zero
    bne t2, t1, fail_5
    csrrw zero, sie, t1
    csrrs t2, sie, zero
    bne t2, t1, fail_6
    addi t1, zero, 0x2
    csrrw zero, sstatus, t1
    la t1, user_wait
    csrrw zero, mepc, t1
    mret

user_wait:
    csrrs t2, sscratch, zero
    beq t2, zero, user_wait

after_irq:
    csrrs t2, sscratch, zero
    addi t3, zero, 1
    bne t2, t3, fail_1

    ld t2, 280(t0)
    blt t2, zero, cause_sign_ok
    beq zero, zero, fail_2

cause_sign_ok:
    andi t2, t2, 255
    addi t3, zero, 5
    bne t2, t3, fail_3

    ld t2, 288(t0)
    la t3, user_wait
    bne t2, t3, fail_4

    addi t6, zero, 42
    sd t6, 256(t0)
    sd zero, 264(t0)
    ebreak

s_handler:
    addi t2, zero, 1
    csrrw zero, sscratch, t2
    csrrs t2, scause, zero
    sd t2, 280(t0)
    csrrs t2, sepc, zero
    sd t2, 288(t0)
    la t2, after_irq
    csrrw zero, sepc, t2
    sret

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
