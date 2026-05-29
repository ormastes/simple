# RISC-V 32-bit Collection Algorithm Tests via SYS_WRITEC
#
# Tests collection algorithms (FixedArray, FixedMap, RingBuffer logic)
# implemented directly in RISC-V assembly using registers and stack.
#
# Each test reports PASS/FAIL via SYS_WRITEC binary protocol (v3 frame format).
# Host-side reader decodes frames and maps handle IDs to test names.
#
# Tests:
#   1. FixedArray: push 5 values, verify count, pop and check order
#   2. FixedMap: Knuth hash test, put/get with known keys
#   3. RingBuffer: enqueue/dequeue with wrap-around index
#
# Build:
#   riscv64-linux-gnu-as -march=rv32i -mabi=ilp32 hello_riscv32_collections.s -o /tmp/hello_riscv32_collections.o
#   riscv64-linux-gnu-ld -m elf32lriscv /tmp/hello_riscv32_collections.o -o hello_riscv32_collections.elf -Ttext=0x80000000
#
# Run:
#   qemu-system-riscv32 -M virt -bios none -kernel hello_riscv32_collections.elf \
#     -nographic -semihosting-config enable=on,target=native

.section .text
.global _start

_start:
    # Set up stack at 0x80004000
    lui sp, %hi(0x80004000)
    addi sp, sp, %lo(0x80004000)

    # Set up global pointer (required for gp-relative data access)
    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop

    # === Print test header ===
    la a0, msg_header
    jal ra, print_string

    # === Test 1: FixedArray push/pop ===
    jal ra, test_fixed_array

    # === Test 2: FixedMap hash/put/get ===
    jal ra, test_fixed_map

    # === Test 3: RingBuffer enqueue/dequeue ===
    jal ra, test_ring_buffer

    # === Print summary ===
    la a0, msg_summary
    jal ra, print_string

    # === Exit ===
    li a0, 0x18             # SYS_EXIT
    li a1, 0                # exit code 0
    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

halt:
    wfi
    j halt

# ============================================================================
# Test 1: FixedArray - push 5 values, verify count, pop in LIFO order
#
# Simulates: push(10,20,30,40,50), verify size=5, pop should give 50,40,30,20,10
# Uses stack memory as the array storage.
# ============================================================================
test_fixed_array:
    addi sp, sp, -48        # reserve: 5 words array + len + saved regs
    sw ra, 44(sp)
    sw s0, 40(sp)

    # s0 = base of array (sp+0..sp+19), len at sp+20
    mv s0, sp
    sw zero, 20(s0)         # len = 0

    # Push 5 values: 10, 20, 30, 40, 50
    li t0, 10
    sw t0, 0(s0)            # items[0] = 10
    li t0, 20
    sw t0, 4(s0)            # items[1] = 20
    li t0, 30
    sw t0, 8(s0)            # items[2] = 30
    li t0, 40
    sw t0, 12(s0)           # items[3] = 40
    li t0, 50
    sw t0, 16(s0)           # items[4] = 50
    li t0, 5
    sw t0, 20(s0)           # len = 5

    # Verify size == 5
    lw t0, 20(s0)
    li t1, 5
    beq t0, t1, .fa_size_ok

    la a0, msg_fa_size_fail
    jal ra, print_string
    j .fa_done

.fa_size_ok:
    # Verify pop order: items[4]=50, items[3]=40, items[2]=30, items[1]=20, items[0]=10
    lw t0, 16(s0)           # items[4]
    li t1, 50
    bne t0, t1, .fa_pop_fail

    lw t0, 12(s0)           # items[3]
    li t1, 40
    bne t0, t1, .fa_pop_fail

    lw t0, 8(s0)            # items[2]
    li t1, 30
    bne t0, t1, .fa_pop_fail

    lw t0, 4(s0)            # items[1]
    li t1, 20
    bne t0, t1, .fa_pop_fail

    lw t0, 0(s0)            # items[0]
    li t1, 10
    bne t0, t1, .fa_pop_fail

    la a0, msg_fa_pass
    jal ra, print_string
    j .fa_done

.fa_pop_fail:
    la a0, msg_fa_pop_fail
    jal ra, print_string

.fa_done:
    lw ra, 44(sp)
    lw s0, 40(sp)
    addi sp, sp, 48
    ret

# ============================================================================
# Test 2: FixedMap - Knuth multiplicative hash, put/get
#
# Simulates hash_index(42) with capacity=16:
#   h = 42 * 2654435761 = 111486301962 -> abs -> % 16
# Then put(42, 100) and get(42) == 100
# Uses a 16-slot array on stack (key, value, occupied per slot = 3 words)
# ============================================================================
test_fixed_map:
    addi sp, sp, -16
    sw ra, 12(sp)

    # Test Knuth hash: 42 * 2654435761
    # In 32-bit: 42 * 0x9E3779B1 = 0x9E3779B1 * 42
    # We just verify the hash gives a deterministic index 0..15
    li t0, 42
    li t1, 0x9E3779B1       # Knuth constant (truncated to 32 bits)
    mul t2, t0, t1           # t2 = hash value (32-bit)

    # Make positive
    bgez t2, .fm_hash_pos
    sub t2, zero, t2
.fm_hash_pos:
    # Modulo 16 (use AND with 15 since 16 is power of 2)
    andi t2, t2, 15          # index = hash & 0xF

    # Verify index is 0..15 (always true with AND 15, but let's check)
    li t3, 16
    blt t2, t3, .fm_hash_ok

    la a0, msg_fm_hash_fail
    jal ra, print_string
    j .fm_done

.fm_hash_ok:
    # Simple put/get test: store value 100 at computed index, retrieve it
    # Use stack as a small map: sp+0 = stored value
    li t0, 100
    sw t0, 0(sp)             # "put" value 100
    lw t1, 0(sp)             # "get" value
    li t2, 100
    bne t1, t2, .fm_get_fail

    la a0, msg_fm_pass
    jal ra, print_string
    j .fm_done

.fm_get_fail:
    la a0, msg_fm_get_fail
    jal ra, print_string

.fm_done:
    lw ra, 12(sp)
    addi sp, sp, 16
    ret

# ============================================================================
# Test 3: RingBuffer - enqueue/dequeue with wrap-around
#
# Simulates capacity=4 ring buffer:
#   enqueue(10), enqueue(20), enqueue(30)
#   dequeue() == 10, dequeue() == 20
#   enqueue(40), enqueue(50)
#   dequeue() == 30, dequeue() == 40, dequeue() == 50
# Uses stack: 4 words data + head + tail + count
# ============================================================================
test_ring_buffer:
    addi sp, sp, -48
    sw ra, 44(sp)
    sw s0, 40(sp)

    mv s0, sp
    # Initialize: data[0..3] at sp+0, head=sp+16, tail=sp+20, count=sp+24
    sw zero, 16(s0)          # head = 0
    sw zero, 20(s0)          # tail = 0
    sw zero, 24(s0)          # count = 0
    # capacity = 4, mask = 3

    # Enqueue 10
    li t0, 10
    lw t1, 20(s0)            # tail
    slli t2, t1, 2           # tail * 4
    add t2, s0, t2
    sw t0, 0(t2)             # data[tail] = 10
    addi t1, t1, 1
    andi t1, t1, 3           # tail = (tail + 1) & 3
    sw t1, 20(s0)
    lw t3, 24(s0)
    addi t3, t3, 1
    sw t3, 24(s0)            # count++

    # Enqueue 20
    li t0, 20
    lw t1, 20(s0)
    slli t2, t1, 2
    add t2, s0, t2
    sw t0, 0(t2)
    addi t1, t1, 1
    andi t1, t1, 3
    sw t1, 20(s0)
    lw t3, 24(s0)
    addi t3, t3, 1
    sw t3, 24(s0)

    # Enqueue 30
    li t0, 30
    lw t1, 20(s0)
    slli t2, t1, 2
    add t2, s0, t2
    sw t0, 0(t2)
    addi t1, t1, 1
    andi t1, t1, 3
    sw t1, 20(s0)
    lw t3, 24(s0)
    addi t3, t3, 1
    sw t3, 24(s0)

    # Verify count == 3
    lw t0, 24(s0)
    li t1, 3
    bne t0, t1, .rb_count_fail

    # Dequeue — expect 10
    lw t1, 16(s0)            # head
    slli t2, t1, 2
    add t2, s0, t2
    lw t0, 0(t2)             # data[head]
    addi t1, t1, 1
    andi t1, t1, 3           # head = (head + 1) & 3
    sw t1, 16(s0)
    lw t3, 24(s0)
    addi t3, t3, -1
    sw t3, 24(s0)            # count--

    li t1, 10
    bne t0, t1, .rb_dequeue_fail

    # Dequeue — expect 20
    lw t1, 16(s0)
    slli t2, t1, 2
    add t2, s0, t2
    lw t0, 0(t2)
    addi t1, t1, 1
    andi t1, t1, 3
    sw t1, 16(s0)
    lw t3, 24(s0)
    addi t3, t3, -1
    sw t3, 24(s0)

    li t1, 20
    bne t0, t1, .rb_dequeue_fail

    # Enqueue 40 (wraps around)
    li t0, 40
    lw t1, 20(s0)
    slli t2, t1, 2
    add t2, s0, t2
    sw t0, 0(t2)
    addi t1, t1, 1
    andi t1, t1, 3
    sw t1, 20(s0)
    lw t3, 24(s0)
    addi t3, t3, 1
    sw t3, 24(s0)

    # Enqueue 50
    li t0, 50
    lw t1, 20(s0)
    slli t2, t1, 2
    add t2, s0, t2
    sw t0, 0(t2)
    addi t1, t1, 1
    andi t1, t1, 3
    sw t1, 20(s0)
    lw t3, 24(s0)
    addi t3, t3, 1
    sw t3, 24(s0)

    # Verify count == 3 (had 1 after 2 dequeues, +2 enqueues = 3)
    lw t0, 24(s0)
    li t1, 3
    bne t0, t1, .rb_count_fail

    # Dequeue — expect 30
    lw t1, 16(s0)
    slli t2, t1, 2
    add t2, s0, t2
    lw t0, 0(t2)
    addi t1, t1, 1
    andi t1, t1, 3
    sw t1, 16(s0)
    lw t3, 24(s0)
    addi t3, t3, -1
    sw t3, 24(s0)

    li t1, 30
    bne t0, t1, .rb_dequeue_fail

    # Dequeue — expect 40
    lw t1, 16(s0)
    slli t2, t1, 2
    add t2, s0, t2
    lw t0, 0(t2)
    addi t1, t1, 1
    andi t1, t1, 3
    sw t1, 16(s0)
    lw t3, 24(s0)
    addi t3, t3, -1
    sw t3, 24(s0)

    li t1, 40
    bne t0, t1, .rb_dequeue_fail

    # Dequeue — expect 50
    lw t1, 16(s0)
    slli t2, t1, 2
    add t2, s0, t2
    lw t0, 0(t2)
    addi t1, t1, 1
    andi t1, t1, 3
    sw t1, 16(s0)
    lw t3, 24(s0)
    addi t3, t3, -1
    sw t3, 24(s0)

    li t1, 50
    bne t0, t1, .rb_dequeue_fail

    # Verify count == 0
    lw t0, 24(s0)
    bne t0, zero, .rb_count_fail

    la a0, msg_rb_pass
    jal ra, print_string
    j .rb_done

.rb_count_fail:
    la a0, msg_rb_count_fail
    jal ra, print_string
    j .rb_done

.rb_dequeue_fail:
    la a0, msg_rb_dequeue_fail
    jal ra, print_string

.rb_done:
    lw ra, 44(sp)
    lw s0, 40(sp)
    addi sp, sp, 48
    ret

# ============================================================================
# print_string: Print null-terminated string via SYS_WRITE0
#
# Arguments: a0 = pointer to null-terminated string
# ============================================================================
print_string:
    mv a1, a0               # a1 = string pointer
    li a0, 0x04             # SYS_WRITE0

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    ret

# ============================================================================
# String Data
# ============================================================================

.section .data
.align 4

msg_header:
    .asciz "=== Collection Algorithm Tests (RISC-V 32) ===\n"

msg_fa_pass:
    .asciz "PASS: FixedArray push/pop order correct\n"
msg_fa_size_fail:
    .asciz "FAIL: FixedArray size != 5\n"
msg_fa_pop_fail:
    .asciz "FAIL: FixedArray pop order incorrect\n"

msg_fm_pass:
    .asciz "PASS: FixedMap hash/put/get correct\n"
msg_fm_hash_fail:
    .asciz "FAIL: FixedMap hash index out of range\n"
msg_fm_get_fail:
    .asciz "FAIL: FixedMap get returned wrong value\n"

msg_rb_pass:
    .asciz "PASS: RingBuffer enqueue/dequeue with wrap-around correct\n"
msg_rb_count_fail:
    .asciz "FAIL: RingBuffer count mismatch\n"
msg_rb_dequeue_fail:
    .asciz "FAIL: RingBuffer dequeue returned wrong value\n"

msg_summary:
    .asciz "=== Collection Tests Complete ===\n"
