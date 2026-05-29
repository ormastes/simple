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
    mv s0, a0
    mv s1, a1

    lui sp, 0x80203
    lui t0, 0x80202
    addi t1, t0, 32
1:
    bgeu t0, t1, 2f
    sd zero, 0(t0)
    addi t0, t0, 8
    j 1b
2:
    mv a0, s0
    mv a1, s1

    li t2, 0x10000000
    li t3, 'S'
    sb t3, 0(t2)
    li t3, 'i'
    sb t3, 0(t2)
    li t3, 'm'
    sb t3, 0(t2)
    li t3, 'p'
    sb t3, 0(t2)
    li t3, 'l'
    sb t3, 0(t2)
    li t3, 'e'
    sb t3, 0(t2)
    li t3, 'O'
    sb t3, 0(t2)
    li t3, 'S'
    sb t3, 0(t2)
    li t3, ' '
    sb t3, 0(t2)
    li t3, 'R'
    sb t3, 0(t2)
    li t3, 'V'
    sb t3, 0(t2)
    li t3, '6'
    sb t3, 0(t2)
    li t3, '4'
    sb t3, 0(t2)
    li t3, 13
    sb t3, 0(t2)
    li t3, 10
    sb t3, 0(t2)

    lui t6, 0x80200
    addi t6, t6, 272
    sd a0, 0(t6)
    sd a1, 8(t6)

    lui t4, 0x80200
    addi t4, t4, 256
    li t5, 42
    sd t5, 0(t4)
    ebreak
