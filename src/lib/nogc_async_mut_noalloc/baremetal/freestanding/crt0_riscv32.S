/* Freestanding crt0, riscv32 (S-mode payload entered from OpenSBI fw_payload:
 * a0 = hartid, a1 = dtb, no stack). Only what Simple cannot express: entry/
 * stack setup, byte load/store, wfi. Serial: 16550 at BM_UART (default
 * 0x10000000 = QEMU virt).
 *
 * ABI (ilp32): the backend lowers Simple i64 to a register pair (lo in the
 * even register, hi in the odd one), so bm_load8(addr: i64) -> i64 takes the
 * address in a0:a1 and returns a0:a1; bm_store8(addr, value) is a0:a1, a2:a3. */
#ifndef BM_UART
#define BM_UART 0x10000000
#endif
    .section .text.boot,"ax"
    .globl _start
_start:
    .option push
    .option norelax
    la sp, bm_stack_top
    .option pop
    andi sp, sp, -16
    call __simple_main
    j bm_halt

    .text
    .globl bm_putc
bm_putc:
    li t0, BM_UART
1:  lbu t1, 5(t0)            /* LSR */
    andi t1, t1, 0x20        /* THRE */
    beqz t1, 1b
    sb a0, 0(t0)
    ret

    .globl bm_load8
bm_load8:
    lbu a0, 0(a0)            /* address low word; high word a1 is 0 on rv32 */
    li a1, 0
    ret

    .globl bm_store8
bm_store8:
    sb a2, 0(a0)             /* value low word is a2 */
    ret

    .globl bm_halt
bm_halt:
    csrci sstatus, 2
1:  wfi
    j 1b

    .globl bm_arena_base
bm_arena_base:
    la a0, bm_arena
    li a1, 0
    ret

    .globl bm_arena_size
bm_arena_size:
    li a0, 65536
    li a1, 0
    ret

    .data
    .balign 16
bm_arena:
    .space 65536
bm_stack:
    .space 65536
bm_stack_top:
