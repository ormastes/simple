# RISC-V 32-bit Cooperative Scheduler Tests via SYS_WRITE0
#
# Tests cooperative scheduling logic (priority-based task execution)
# implemented directly in RISC-V assembly using registers and stack.
#
# Simulates NoallocScheduler behavior:
#   - 3 tasks with different priorities (low=1, medium=2, high=3)
#   - Round-robin within same priority level
#   - Higher priority tasks run first
#   - Tasks decrement a "work counter" each tick; complete when counter reaches 0
#
# Build:
#   riscv64-linux-gnu-as -march=rv32i -mabi=ilp32 hello_riscv32_scheduler.s -o /tmp/hello_riscv32_scheduler.o
#   riscv64-linux-gnu-ld -m elf32lriscv /tmp/hello_riscv32_scheduler.o -o hello_riscv32_scheduler.elf -Ttext=0x80000000
#
# Run:
#   qemu-system-riscv32 -M virt -bios none -kernel hello_riscv32_scheduler.elf \
#     -nographic -semihosting-config enable=on,target=native

.section .text
.global _start

# Task state layout (3 words per task):
#   +0: priority (1=low, 2=medium, 3=high)
#   +4: remaining_work (ticks to completion)
#   +8: completed (0=no, 1=yes)

.equ TASK_PRIORITY, 0
.equ TASK_WORK, 4
.equ TASK_DONE, 8
.equ TASK_SIZE, 12
.equ NUM_TASKS, 3

_start:
    lui sp, %hi(0x80004000)
    addi sp, sp, %lo(0x80004000)

    la a0, msg_header
    jal ra, print_string

    # === Test 1: Priority ordering ===
    jal ra, test_priority_order

    # === Test 2: All tasks complete ===
    jal ra, test_all_complete

    # === Test 3: Tick count ===
    jal ra, test_tick_count

    la a0, msg_summary
    jal ra, print_string

    # Exit
    li a0, 0x18
    li a1, 0
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
# Test 1: Priority ordering
#
# Initialize 3 tasks: high(pri=3,work=1), medium(pri=2,work=1), low(pri=1,work=1)
# Run scheduler — high should complete first
# ============================================================================
test_priority_order:
    addi sp, sp, -64
    sw ra, 60(sp)
    sw s0, 56(sp)
    sw s1, 52(sp)
    sw s2, 48(sp)

    mv s0, sp               # s0 = task array base

    # Task 0: low priority
    li t0, 1                 # priority = 1
    sw t0, 0(s0)
    li t0, 1                 # work = 1
    sw t0, 4(s0)
    sw zero, 8(s0)           # completed = 0

    # Task 1: medium priority
    li t0, 2
    sw t0, 12(s0)
    li t0, 1
    sw t0, 16(s0)
    sw zero, 20(s0)

    # Task 2: high priority
    li t0, 3
    sw t0, 24(s0)
    li t0, 1
    sw t0, 28(s0)
    sw zero, 32(s0)

    # s1 = completion order index (0-based)
    li s1, 0
    # s2 = completion_order array at sp+36 (3 words)

    # Run scheduler: find highest priority incomplete task, run it
.po_tick:
    # Find highest priority incomplete task
    li t3, -1               # best_idx = -1
    li t4, 0                # best_priority = 0

    # Check task 0
    lw t0, 8(s0)            # task[0].completed
    bne t0, zero, .po_check1
    lw t0, 0(s0)            # task[0].priority
    ble t0, t4, .po_check1
    li t3, 0                # best_idx = 0
    mv t4, t0               # best_priority = pri

.po_check1:
    lw t0, 20(s0)           # task[1].completed
    bne t0, zero, .po_check2
    lw t0, 12(s0)           # task[1].priority
    ble t0, t4, .po_check2
    li t3, 1
    mv t4, t0

.po_check2:
    lw t0, 32(s0)           # task[2].completed
    bne t0, zero, .po_run
    lw t0, 24(s0)           # task[2].priority
    ble t0, t4, .po_run
    li t3, 2
    mv t4, t0

.po_run:
    # If no task found, done
    li t0, -1
    beq t3, t0, .po_check_order

    # Run selected task: decrement work
    li t0, TASK_SIZE
    mul t1, t3, t0           # offset = best_idx * TASK_SIZE
    add t1, s0, t1           # t1 = &task[best_idx]
    lw t0, TASK_WORK(t1)
    addi t0, t0, -1
    sw t0, TASK_WORK(t1)

    # If work == 0, mark completed and record order
    bne t0, zero, .po_tick
    li t0, 1
    sw t0, TASK_DONE(t1)

    # Record completion order
    slli t2, s1, 2           # order_idx * 4
    addi t2, t2, 36          # offset into completion array
    add t2, s0, t2
    sw t3, 0(t2)             # completion_order[s1] = task_idx
    addi s1, s1, 1

    j .po_tick

.po_check_order:
    # Verify: completion_order[0] should be task 2 (high priority)
    lw t0, 36(s0)            # first completed
    li t1, 2                 # expect task 2 (highest priority)
    bne t0, t1, .po_fail

    la a0, msg_po_pass
    jal ra, print_string
    j .po_done

.po_fail:
    la a0, msg_po_fail
    jal ra, print_string

.po_done:
    lw ra, 60(sp)
    lw s0, 56(sp)
    lw s1, 52(sp)
    lw s2, 48(sp)
    addi sp, sp, 64
    ret

# ============================================================================
# Test 2: All tasks complete
#
# 3 tasks with work=2,3,1 — all must complete after enough ticks
# ============================================================================
test_all_complete:
    addi sp, sp, -48
    sw ra, 44(sp)
    sw s0, 40(sp)

    mv s0, sp

    # Task 0: pri=1, work=2
    li t0, 1
    sw t0, 0(s0)
    li t0, 2
    sw t0, 4(s0)
    sw zero, 8(s0)

    # Task 1: pri=2, work=3
    li t0, 2
    sw t0, 12(s0)
    li t0, 3
    sw t0, 16(s0)
    sw zero, 20(s0)

    # Task 2: pri=3, work=1
    li t0, 3
    sw t0, 24(s0)
    li t0, 1
    sw t0, 28(s0)
    sw zero, 32(s0)

    # Run up to 20 ticks
    li s1, 0                 # tick counter

.ac_tick:
    li t0, 20
    bge s1, t0, .ac_check    # safety limit

    # Find highest priority incomplete task
    li t3, -1
    li t4, 0

    lw t0, 8(s0)
    bne t0, zero, .ac_c1
    lw t0, 0(s0)
    ble t0, t4, .ac_c1
    li t3, 0
    mv t4, t0
.ac_c1:
    lw t0, 20(s0)
    bne t0, zero, .ac_c2
    lw t0, 12(s0)
    ble t0, t4, .ac_c2
    li t3, 1
    mv t4, t0
.ac_c2:
    lw t0, 32(s0)
    bne t0, zero, .ac_run
    lw t0, 24(s0)
    ble t0, t4, .ac_run
    li t3, 2
    mv t4, t0

.ac_run:
    li t0, -1
    beq t3, t0, .ac_check    # all done

    li t0, TASK_SIZE
    mul t1, t3, t0
    add t1, s0, t1
    lw t0, TASK_WORK(t1)
    addi t0, t0, -1
    sw t0, TASK_WORK(t1)
    bne t0, zero, .ac_next
    li t0, 1
    sw t0, TASK_DONE(t1)

.ac_next:
    addi s1, s1, 1
    j .ac_tick

.ac_check:
    # Verify all 3 tasks completed
    lw t0, 8(s0)             # task[0].completed
    beq t0, zero, .ac_fail
    lw t0, 20(s0)            # task[1].completed
    beq t0, zero, .ac_fail
    lw t0, 32(s0)            # task[2].completed
    beq t0, zero, .ac_fail

    la a0, msg_ac_pass
    jal ra, print_string
    j .ac_done

.ac_fail:
    la a0, msg_ac_fail
    jal ra, print_string

.ac_done:
    lw ra, 44(sp)
    lw s0, 40(sp)
    addi sp, sp, 48
    ret

# ============================================================================
# Test 3: Tick count matches total work
#
# 3 tasks with work=1,2,3 — total ticks should be 6
# ============================================================================
test_tick_count:
    addi sp, sp, -48
    sw ra, 44(sp)
    sw s0, 40(sp)

    mv s0, sp

    # Task 0: pri=1, work=1
    li t0, 1
    sw t0, 0(s0)
    li t0, 1
    sw t0, 4(s0)
    sw zero, 8(s0)

    # Task 1: pri=2, work=2
    li t0, 2
    sw t0, 12(s0)
    li t0, 2
    sw t0, 16(s0)
    sw zero, 20(s0)

    # Task 2: pri=3, work=3
    li t0, 3
    sw t0, 24(s0)
    li t0, 3
    sw t0, 28(s0)
    sw zero, 32(s0)

    li s1, 0                 # tick counter

.tc_tick:
    li t0, 20
    bge s1, t0, .tc_check

    li t3, -1
    li t4, 0

    lw t0, 8(s0)
    bne t0, zero, .tc_c1
    lw t0, 0(s0)
    ble t0, t4, .tc_c1
    li t3, 0
    mv t4, t0
.tc_c1:
    lw t0, 20(s0)
    bne t0, zero, .tc_c2
    lw t0, 12(s0)
    ble t0, t4, .tc_c2
    li t3, 1
    mv t4, t0
.tc_c2:
    lw t0, 32(s0)
    bne t0, zero, .tc_run
    lw t0, 24(s0)
    ble t0, t4, .tc_run
    li t3, 2
    mv t4, t0

.tc_run:
    li t0, -1
    beq t3, t0, .tc_check

    li t0, TASK_SIZE
    mul t1, t3, t0
    add t1, s0, t1
    lw t0, TASK_WORK(t1)
    addi t0, t0, -1
    sw t0, TASK_WORK(t1)
    bne t0, zero, .tc_next
    li t0, 1
    sw t0, TASK_DONE(t1)

.tc_next:
    addi s1, s1, 1
    j .tc_tick

.tc_check:
    # Total ticks should be 6 (1+2+3)
    li t0, 6
    bne s1, t0, .tc_fail

    la a0, msg_tc_pass
    jal ra, print_string
    j .tc_done

.tc_fail:
    la a0, msg_tc_fail
    jal ra, print_string

.tc_done:
    lw ra, 44(sp)
    lw s0, 40(sp)
    addi sp, sp, 48
    ret

# ============================================================================
# print_string: Print null-terminated string via SYS_WRITE0
# ============================================================================
print_string:
    mv a1, a0
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
    .asciz "=== Scheduler Tests (RISC-V 32) ===\n"

msg_po_pass:
    .asciz "PASS: highest priority task completes first\n"
msg_po_fail:
    .asciz "FAIL: priority ordering incorrect\n"

msg_ac_pass:
    .asciz "PASS: all tasks complete after sufficient ticks\n"
msg_ac_fail:
    .asciz "FAIL: not all tasks completed\n"

msg_tc_pass:
    .asciz "PASS: tick count matches total work (6 ticks)\n"
msg_tc_fail:
    .asciz "FAIL: tick count mismatch\n"

msg_summary:
    .asciz "=== Scheduler Tests Complete ===\n"
