.section .text.fw, "ax"
.globl _start
_start:
    lui t0, 0x1
    addi t0, t0, 4
    slli t0, t0, 19
    csrw mepc, t0
    addi t0, zero, 1
    slli t0, t0, 11
    csrw mstatus, t0
    mret

.section .text.payload, "ax"
.globl payload_start
payload_start:
    lui t6, 0x1
    addi t6, t6, 4
    slli t6, t6, 19
    addi t6, t6, 272
    sd a0, 0(t6)
    sd a1, 8(t6)

    li t2, 0x10000000
    li t3, 'S'
    sb t3, 0(t2)
    li t3, 'B'
    sb t3, 0(t2)
    li t3, 'O'
    sb t3, 0(t2)
    li t3, 'T'
    sb t3, 0(t2)

    lui t4, 0x1
    addi t4, t4, 4
    slli t4, t4, 19
    addi t4, t4, 256
    li t5, 42
    sd t5, 0(t4)
    ebreak
