    .section .text
    .globl _start
_start:
    lui t0, 0x80000
    addi t1, zero, 42
    sd t1, 256(t0)
    ld t2, 256(t0)
    addi t3, zero, 42
    bne t2, t3, fail
    sd zero, 264(t0)
    ebreak

fail:
    addi t4, zero, 1
    sd t4, 264(t0)
    ebreak
