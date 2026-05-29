    .section .text
    .globl _start
_start:
    lui t0, 0x80000
    la t1, s_handler
    csrrw zero, stvec, t1
    addi t1, zero, 0x100
    csrrw zero, medeleg, t1
    la t1, user_start
    csrrw zero, mepc, t1
    csrrw zero, mstatus, zero
    mret

user_start:
user_ecall:
    ecall

after_user:
    ld t2, 272(t0)
    addi t3, zero, 1
    bne t2, t3, fail_1

    ld t2, 280(t0)
    addi t3, zero, 8
    bne t2, t3, fail_2

    ld t2, 288(t0)
    la t3, user_ecall
    bne t2, t3, fail_3

    addi t6, zero, 42
    sd t6, 256(t0)
    sd zero, 264(t0)
    ebreak

s_handler:
    addi t2, zero, 1
    sd t2, 272(t0)
    csrrs t2, scause, zero
    sd t2, 280(t0)
    csrrs t2, sepc, zero
    sd t2, 288(t0)
    la t2, after_user
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
