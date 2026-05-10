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
    li sp, 0x80204000

    la t6, proof_a0
    sd s0, 0(t6)
    sd s1, 8(t6)

    mv a0, s1
    jal ra, parse_minimal_dtb
    mv s2, a0
    mv s3, a1
    mv s4, a2
    mv s5, a3
    mv s6, a4

    la t6, proof_dtb_valid
    sd s2, 0(t6)
    sd s3, 8(t6)
    sd s4, 16(t6)
    sd s5, 24(t6)
    sd s6, 32(t6)

    li t0, 1
    bne s2, t0, fail
    li t0, 0x80000000
    bne s3, t0, fail
    li t0, 0x08000000
    bne s4, t0, fail
    li t0, 0x10000000
    bne s5, t0, fail

    li t2, 0x10000000
    li t3, 'D'
    sb t3, 0(t2)
    li t3, 'T'
    sb t3, 0(t2)
    li t3, 'B'
    sb t3, 0(t2)
    li t3, 'R'
    sb t3, 0(t2)

    la t4, proof_pass
    li t5, 42
    sd t5, 0(t4)
    ebreak

fail:
    li t2, 0x10000000
    li t3, 'F'
    sb t3, 0(t2)
    li t3, 'A'
    sb t3, 0(t2)
    li t3, 'I'
    sb t3, 0(t2)
    li t3, 'L'
    sb t3, 0(t2)
    ebreak

parse_minimal_dtb:
    addi sp, sp, -104
    sd ra, 0(sp)
    sd s4, 8(sp)
    sd s5, 16(sp)
    sd s6, 24(sp)
    sd s7, 32(sp)
    sd s8, 40(sp)
    sd s9, 48(sp)
    sd s10, 56(sp)
    sd s11, 64(sp)
    sd s0, 72(sp)
    sd s1, 80(sp)
    sd s2, 88(sp)
    sd s3, 96(sp)

    mv s7, a0
    mv s8, zero
    mv s9, zero
    mv s10, zero
    mv s11, zero
    mv s4, zero

    mv a0, s7
    jal ra, read_be32
    li t0, 0xD00DFEED
    bne a0, t0, parse_fail

    addi a0, s7, 20
    jal ra, read_be32
    li t0, 17
    bltu a0, t0, parse_fail

    addi a0, s7, 8
    jal ra, read_be32
    add s0, s7, a0

    addi a0, s7, 12
    jal ra, read_be32
    add s1, s7, a0

    addi a0, s7, 36
    jal ra, read_be32
    beq a0, zero, parse_fail
    add s2, s0, a0

    mv s3, s0
dtb_loop:
    bgeu s3, s2, parse_done
    mv a0, s3
    jal ra, read_be32
    mv t0, a0
    addi s3, s3, 4

    li t1, 1
    beq t0, t1, handle_begin_node
    li t1, 2
    beq t0, t1, handle_end_node
    li t1, 3
    beq t0, t1, handle_prop
    li t1, 4
    beq t0, t1, dtb_loop
    li t1, 9
    beq t0, t1, parse_done
    j parse_fail

handle_begin_node:
    mv a0, s3
    jal ra, classify_node
    mv s8, a0
    mv a0, s3
    jal ra, skip_c_string_aligned
    mv s3, a0
    j dtb_loop

handle_end_node:
    mv s8, zero
    j dtb_loop

handle_prop:
    mv a0, s3
    jal ra, read_be32
    mv t2, a0
    addi a0, s3, 4
    jal ra, read_be32
    add t3, s1, a0
    addi t4, s3, 8

    mv a0, t3
    jal ra, is_reg_prop
    beq a0, zero, prop_advance

    li t0, 1
    beq s8, t0, prop_memory
    li t0, 2
    beq s8, t0, prop_serial
    j prop_advance

prop_memory:
    li t0, 16
    bltu t2, t0, prop_advance
    bne s4, zero, prop_advance
    mv a0, t4
    jal ra, read_be64
    mv s9, a0
    addi a0, t4, 8
    jal ra, read_be64
    mv s10, a0
    li s4, 1
    j prop_advance

prop_serial:
    li t0, 16
    bltu t2, t0, prop_advance
    bne s11, zero, prop_advance
    mv a0, t4
    jal ra, read_be64
    mv s11, a0
    j prop_advance

prop_advance:
    add s3, t4, t2
    mv a0, s3
    jal ra, align4
    mv s3, a0
    j dtb_loop

parse_done:
    mv a0, s4
    mv a1, s9
    mv a2, s10
    mv a3, s11
    mv a4, zero
parse_return:
    ld ra, 0(sp)
    ld s4, 8(sp)
    ld s5, 16(sp)
    ld s6, 24(sp)
    ld s7, 32(sp)
    ld s8, 40(sp)
    ld s9, 48(sp)
    ld s10, 56(sp)
    ld s11, 64(sp)
    ld s0, 72(sp)
    ld s1, 80(sp)
    ld s2, 88(sp)
    ld s3, 96(sp)
    addi sp, sp, 104
    ret

parse_fail:
    mv a0, zero
    mv a1, zero
    mv a2, zero
    mv a3, zero
    mv a4, zero
    j parse_return

read_be32:
    lbu t0, 0(a0)
    lbu t1, 1(a0)
    lbu t2, 2(a0)
    lbu t3, 3(a0)
    slli t0, t0, 24
    slli t1, t1, 16
    slli t2, t2, 8
    or t0, t0, t1
    or t0, t0, t2
    or a0, t0, t3
    ret

read_be64:
    addi sp, sp, -16
    sd ra, 0(sp)
    sd a0, 8(sp)
    jal ra, read_be32
    mv t0, a0
    ld a0, 8(sp)
    addi a0, a0, 4
    jal ra, read_be32
    slli t0, t0, 32
    or a0, t0, a0
    ld ra, 0(sp)
    addi sp, sp, 16
    ret

align4:
    addi a0, a0, 3
    andi a0, a0, -4
    ret

skip_c_string_aligned:
    mv t0, a0
1:
    lbu t1, 0(t0)
    addi t0, t0, 1
    bne t1, zero, 1b
    addi a0, t0, 3
    andi a0, a0, -4
    ret

classify_node:
    lbu t0, 0(a0)
    beq t0, zero, classify_other
    li t1, 'm'
    bne t0, t1, check_serial
    lbu t0, 1(a0)
    li t1, 'e'
    bne t0, t1, classify_other
    lbu t0, 2(a0)
    li t1, 'm'
    bne t0, t1, classify_other
    lbu t0, 3(a0)
    li t1, 'o'
    bne t0, t1, classify_other
    lbu t0, 4(a0)
    li t1, 'r'
    bne t0, t1, classify_other
    lbu t0, 5(a0)
    li t1, 'y'
    bne t0, t1, classify_other
    lbu t0, 6(a0)
    li t1, '@'
    bne t0, t1, classify_other
    li a0, 1
    ret
check_serial:
    lbu t0, 0(a0)
    li t1, 's'
    bne t0, t1, classify_other
    lbu t0, 1(a0)
    li t1, 'e'
    bne t0, t1, classify_other
    lbu t0, 2(a0)
    li t1, 'r'
    bne t0, t1, classify_other
    lbu t0, 3(a0)
    li t1, 'i'
    bne t0, t1, classify_other
    lbu t0, 4(a0)
    li t1, 'a'
    bne t0, t1, classify_other
    lbu t0, 5(a0)
    li t1, 'l'
    bne t0, t1, classify_other
    lbu t0, 6(a0)
    li t1, '@'
    bne t0, t1, classify_other
    li a0, 2
    ret
classify_other:
    mv a0, zero
    ret

is_reg_prop:
    lbu t0, 0(a0)
    li t1, 'r'
    bne t0, t1, not_reg_prop
    lbu t0, 1(a0)
    li t1, 'e'
    bne t0, t1, not_reg_prop
    lbu t0, 2(a0)
    li t1, 'g'
    bne t0, t1, not_reg_prop
    lbu t0, 3(a0)
    bne t0, zero, not_reg_prop
    li a0, 1
    ret
not_reg_prop:
    mv a0, zero
    ret

.org 0x800
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
proof_uart_base:
    .dword 0
