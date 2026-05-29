    .section .text
    .option push
    .option rvc
    .globl _start
_start:
    c.addi sp, 4
    c.li t1, 21
    c.slli t1, 1
    c.sdsp t1, 0(sp)
    c.ldsp t2, 0(sp)
    c.li t3, 21
    c.slli t3, 1
    bne t2, t3, fail
    lui t0, 0x80000
    sd t2, 256(t0)
    sd zero, 264(t0)
    ebreak

fail:
    lui t0, 0x80000
    addi t4, zero, 1
    sd t4, 264(t0)
    ebreak
    .option pop
