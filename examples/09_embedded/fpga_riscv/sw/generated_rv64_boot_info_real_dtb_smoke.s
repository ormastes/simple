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

    la t6, proof_a0
    sd s0, 0(t6)
    sd s1, 8(t6)

    lbu t0, 0(s1)
    li t1, 0xD0
    bne t0, t1, fail
    lbu t0, 1(s1)
    li t1, 0x0D
    bne t0, t1, fail
    lbu t0, 2(s1)
    li t1, 0xFE
    bne t0, t1, fail
    lbu t0, 3(s1)
    li t1, 0xED
    bne t0, t1, fail

    addi t0, s1, 0x60
    li t1, 0
    lbu t2, 0(t0)
    slli t1, t1, 8
    or t1, t1, t2
    lbu t2, 1(t0)
    slli t1, t1, 8
    or t1, t1, t2
    lbu t2, 2(t0)
    slli t1, t1, 8
    or t1, t1, t2
    lbu t2, 3(t0)
    slli t1, t1, 8
    or t1, t1, t2
    lbu t2, 4(t0)
    slli t1, t1, 8
    or t1, t1, t2
    lbu t2, 5(t0)
    slli t1, t1, 8
    or t1, t1, t2
    lbu t2, 6(t0)
    slli t1, t1, 8
    or t1, t1, t2
    lbu t2, 7(t0)
    slli t1, t1, 8
    or t1, t1, t2

    addi t0, s1, 0x68
    li t3, 0
    lbu t2, 0(t0)
    slli t3, t3, 8
    or t3, t3, t2
    lbu t2, 1(t0)
    slli t3, t3, 8
    or t3, t3, t2
    lbu t2, 2(t0)
    slli t3, t3, 8
    or t3, t3, t2
    lbu t2, 3(t0)
    slli t3, t3, 8
    or t3, t3, t2
    lbu t2, 4(t0)
    slli t3, t3, 8
    or t3, t3, t2
    lbu t2, 5(t0)
    slli t3, t3, 8
    or t3, t3, t2
    lbu t2, 6(t0)
    slli t3, t3, 8
    or t3, t3, t2
    lbu t2, 7(t0)
    slli t3, t3, 8
    or t3, t3, t2

    li t4, 1
    la t2, proof_dtb_valid
    sd t4, 0(t2)
    la t2, proof_ram_base
    sd t1, 0(t2)
    la t2, proof_ram_size
    sd t3, 0(t2)

    li t2, 0x10000000
    li t4, 'D'
    sb t4, 0(t2)
    li t4, 'T'
    sb t4, 0(t2)
    li t4, 'B'
    sb t4, 0(t2)
    li t4, 'R'
    sb t4, 0(t2)

    la t5, proof_pass
    li t4, 42
    sd t4, 0(t5)
    ebreak

fail:
    li t2, 0x10000000
    li t4, 'F'
    sb t4, 0(t2)
    li t4, 'A'
    sb t4, 0(t2)
    li t4, 'I'
    sb t4, 0(t2)
    li t4, 'L'
    sb t4, 0(t2)
    ebreak

.org 0x400
proof_pass:
    .dword 0
    .dword 0
proof_a0:
    .dword 0
proof_a1:
    .dword 0
proof_dtb_valid:
    .dword 0
proof_ram_base:
    .dword 0
proof_ram_size:
    .dword 0
