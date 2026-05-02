    .section .text
    .globl _start
_start:
    lui t0, 0x80000

    addi t1, zero, 7
    addi t2, zero, 7
    beq t1, t2, beq_ok
    addi t3, zero, 1
    sd t3, 264(t0)
    ebreak

beq_ok:
    bne t1, t2, fail_2

    addi t3, zero, -1
    addi t4, zero, 1
    blt t3, t4, blt_ok
    addi t3, zero, 3
    sd t3, 264(t0)
    ebreak

blt_ok:
    bge t4, t3, bge_ok
    addi t3, zero, 3
    sd t3, 264(t0)
    ebreak

bge_ok:
    bltu t4, t3, bltu_ok
    addi t3, zero, 4
    sd t3, 264(t0)
    ebreak

bltu_ok:
    bgeu t3, t4, branch_done
    addi t3, zero, 4
    sd t3, 264(t0)
    ebreak

branch_done:
    la s0, jal_return
    jal ra, jal_target

jal_return:
    la s2, after_jalr_call
    la s1, jalr_pad
    jalr ra, s1, 4

after_jalr_call:
    addi t5, zero, 42
    sd t5, 256(t0)
    sd zero, 264(t0)
    ebreak

jal_target:
    bne ra, s0, fail_5
    jalr zero, ra, 0

jalr_pad:
    addi zero, zero, 0

jalr_target:
    bne ra, s2, fail_6
    jalr zero, ra, 0

fail_2:
    addi t3, zero, 2
    sd t3, 264(t0)
    ebreak

fail_5:
    addi t3, zero, 5
    sd t3, 264(t0)
    ebreak

fail_6:
    addi t3, zero, 6
    sd t3, 264(t0)
    ebreak
