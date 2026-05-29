    .section .text
    .globl _start
_start:
    lui t0, 0x80000
    addi t1, zero, 0x20
    csrrw zero, mideleg, t1
    la t1, s_poll
    csrrw zero, mepc, t1
    csrrw zero, mstatus, zero
    mret

s_poll:
    addi t3, zero, 64
wait_sip:
    csrrs t2, sip, zero
    andi t2, t2, 0x20
    bne t2, zero, got_sip
    addi t3, t3, -1
    bne t3, zero, wait_sip
    beq zero, zero, fail_1

got_sip:
    addi t6, zero, 42
    sd t6, 256(t0)
    sd zero, 264(t0)
    ebreak

fail_1:
    addi t6, zero, 1
    sd t6, 264(t0)
    ebreak
