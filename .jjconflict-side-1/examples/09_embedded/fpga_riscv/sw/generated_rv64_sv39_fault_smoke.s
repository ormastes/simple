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
    li t0, 0x8000000000000001
    csrrw zero, satp, t0
    sfence.vma x0, x0

    li t1, 0x40000000
    lw t3, 256(t1)
    ebreak

trap_handler:
    csrrs t6, mcause, zero
    sd t6, 256(zero)
    csrrs t6, mtval, zero
    sd t6, 264(zero)
    ebreak
