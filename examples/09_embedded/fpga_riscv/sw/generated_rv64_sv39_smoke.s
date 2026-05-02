    .section .text
    .globl _start
_start:
    la t6, trap_handler
    csrrw zero, mtvec, t6
    li t0, 0x800
    csrrw zero, mstatus, t0
    la t0, s_mode_entry
    csrrw zero, mepc, t0
    mret

s_mode_entry:
    addi t5, zero, 42
    sd t5, 256(zero)
    sd zero, 264(zero)

    li t0, 0x8000000000000001
    csrrw zero, satp, t0
    csrrs t4, satp, zero
    bne t4, t0, fail_satp
    sfence.vma x0, x0

    li t1, 0x40000000
    lw t3, 256(t1)
    addi zero, zero, 0
    csrrw zero, satp, zero
    sd t3, 264(zero)
    ebreak

fail:
    addi t4, zero, 1
    sd t4, 264(zero)
    ebreak

fail_satp:
    addi t4, zero, 2
    sd t4, 264(zero)
    ebreak

trap_handler:
    csrrs t6, mcause, zero
    sd t6, 272(zero)
    csrrs t6, mtval, zero
    sd t6, 280(zero)
    ebreak
