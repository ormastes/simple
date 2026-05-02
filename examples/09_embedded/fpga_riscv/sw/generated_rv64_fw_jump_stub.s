.section .text, "ax"
.globl _start
_start:
    li t0, 0x80200000
    csrw mepc, t0
    li t0, 0x00000800
    csrw mstatus, t0
    mret
