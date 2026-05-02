    .section .text
    .globl _start
_start:
    lui t0, 0x80000
    la t1, trap_handler
    csrrw zero, mtvec, t1
    csrrw zero, mscratch, zero

ecall_site:
    ecall

after_ecall:
    csrrs t2, mscratch, zero
    addi t3, zero, 1
    bne t2, t3, fail_1

    csrrs t2, mcause, zero
    addi t3, zero, 8
    bne t2, t3, fail_2

    la t4, ecall_site
    ld t5, 272(t0)
    bne t5, t4, fail_3

    la t4, after_ecall
    csrrs t5, mepc, zero
    bne t5, t4, fail_4

    addi t6, zero, 42
    sd t6, 256(t0)
    sd zero, 264(t0)
    ebreak

trap_handler:
    csrrs t2, mepc, zero
    sd t2, 272(t0)
    addi t2, t2, 4
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
