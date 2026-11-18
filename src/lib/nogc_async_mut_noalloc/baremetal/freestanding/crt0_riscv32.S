/* Freestanding crt0, riscv32 (S-mode payload entered from OpenSBI fw_payload:
 * a0 = hartid, a1 = dtb, no stack). Only what Simple cannot express: entry/
 * stack setup, byte load/store, wfi. Serial: 16550 at BM_UART (default
 * 0x10000000 = QEMU virt).
 * ABI: bm_rt32.spl declares the 32-bit widths the backend emits, so every
 * argument is one register (bm_store8 value in a1). */
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
    lbu a0, 0(a0)
    ret

    .globl bm_store8
bm_store8:
    sb a1, 0(a0)             /* value: 32-bit arg in a1 */
    ret

    .globl bm_halt
bm_halt:
    csrci sstatus, 2
1:  wfi
    j 1b

    .globl bm_arena_base
bm_arena_base:
    la a0, bm_arena
    ret

    .globl bm_arena_size
bm_arena_size:
    li a0, 65536
    ret

    .data
    .balign 16
bm_arena:
    .space 65536
bm_stack:
    .space 65536
bm_stack_top:
