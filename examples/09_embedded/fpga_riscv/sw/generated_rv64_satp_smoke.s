    .section .text
    .globl _start
_start:
    lui t0, 0x80000

    li t1, 0x8000000000080000
    csrrw zero, satp, t1
    csrrs t2, satp, zero
    bne t2, t1, fail_1

    sfence.vma x0, x0

    csrrw zero, satp, zero
    csrrs t2, satp, zero
    bne t2, zero, fail_2

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
