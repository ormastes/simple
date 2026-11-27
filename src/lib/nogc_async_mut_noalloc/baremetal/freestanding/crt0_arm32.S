/* Freestanding crt0, ARMv7-A 32-bit (ARM state, entered from a UEFI loader stub).
 * Only what Simple cannot express: entry/stack setup, byte load/store, wfi.
 * Serial: PL011 at BM_UART (default 0x09000000 = QEMU virt; set -DBM_UART=
 * for a board). Position independent (pc-relative literals, no absolute relocs).
 * Simple i64 args/results follow AAPCS: an i64 is the register pair r0:r1 (then
 * r2:r3); the high word of every address/byte value here is zero. */
#ifndef BM_UART
#define BM_UART 0x09000000
#endif
    .arm
    .section .text.boot,"ax"
    .globl _start
_start:
    ldr r0, 2f
1:  add r0, r0, pc           /* pc reads as 1b + 8 */
    bic r0, r0, #7
    mov sp, r0
    bl __simple_main
    b bm_halt
2:  .word bm_stack_top - (1b + 8)

    .text
    .globl bm_putc
bm_putc:
    ldr r1, =BM_UART
1:  ldr r2, [r1, #0x18]      /* UARTFR */
    tst r2, #0x20            /* TXFF */
    bne 1b
    strb r0, [r1]
    bx lr

    .globl bm_load8
bm_load8:
    ldrb r0, [r0]
    mov r1, #0
    bx lr

    .globl bm_store8
bm_store8:
    strb r2, [r0]
    bx lr

    .globl bm_halt
bm_halt:
    cpsid if
1:  wfi
    b 1b

    .globl bm_arena_base
bm_arena_base:
    ldr r0, 2f
1:  add r0, r0, pc
    mov r1, #0
    bx lr
2:  .word bm_arena - (1b + 8)

    .globl bm_arena_size
bm_arena_size:
    mov r0, #65536
    mov r1, #0
    bx lr

    .ltorg
    .data
    .balign 16
bm_arena:
    .space 65536
bm_stack:
    .space 65536
bm_stack_top:

/* ABI shims. The native arm32 backend passes pointer/handle arguments to the
 * rt_* entry points as 32-bit values (AAPCS: ptr in r0, i64 length in r2:r3,
 * two handles in r0/r1), but bm_rt.spl declares them i64 (r0:r1, r2:r3), so
 * the high word r1 would be garbage. Each plain rt_* name is therefore this
 * shim: zero-extend the 32-bit args, then tail-call the bm_rt body, which the
 * boot check renames to bm32_<name>. i64 results come back in r0:r1 (the
 * caller reads r0 for handles, r0:r1 for i64). */
    .text
    .macro RT_SHIM name
    .globl \name
\name:
    mov r1, #0
    b bm32_\name
    .endm
    RT_SHIM rt_string_new
    RT_SHIM rt_string_new_literal
    RT_SHIM rt_string_data
    RT_SHIM rt_string_len
    RT_SHIM rt_interp_cstr
    RT_SHIM rt_println_str
    RT_SHIM rt_println
    RT_SHIM rt_panic

    .globl rt_strcat_tagged
rt_strcat_tagged:
    mov r2, r1
    mov r3, #0
    mov r1, #0
    b bm32_rt_strcat_tagged

    .globl rt_raw_i64_to_string
rt_raw_i64_to_string:
    b bm32_rt_raw_i64_to_string
