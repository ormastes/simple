/* Freestanding crt0, aarch64 (EL1/EL2, entered from a UEFI loader stub).
 * Only what Simple cannot express: entry/stack setup, byte load/store, wfi.
 * Serial: PL011 at BM_UART (default 0x09000000 = QEMU virt; set -DBM_UART=
 * for a board). Position independent (adr). */
#ifndef BM_UART
#define BM_UART 0x09000000
#endif
    .section .text.boot,"ax"
    .globl _start
_start:
    adr x0, bm_stack_top
    and x0, x0, #~15
    mov sp, x0
    bl __simple_main
    b bm_halt

    .text
    .globl bm_putc
bm_putc:
    ldr x1, =BM_UART
1:  ldr w2, [x1, #0x18]      /* UARTFR */
    tbnz w2, #5, 1b          /* TXFF */
    strb w0, [x1]
    ret

    .globl bm_load8
bm_load8:
    ldrb w0, [x0]
    ret

    .globl bm_store8
bm_store8:
    strb w1, [x0]
    ret

    .globl bm_halt
bm_halt:
    msr daifset, #0xf
1:  wfi
    b 1b

    .globl bm_arena_base
bm_arena_base:
    adr x0, bm_arena
    ret

    .globl bm_arena_size
bm_arena_size:
    mov x0, #65536
    ret

    .ltorg
    .data
    .balign 16
bm_arena:
    .space 65536
bm_stack:
    .space 65536
bm_stack_top:
