/* Freestanding crt0, i686 (IA32 protected mode, entered from a UEFI IA32 loader stub).
 * Only what Simple cannot express: entry/stack switch, port I/O, byte
 * load/store, hlt. Everything else lives in bm_rt.spl.
 * Serial: 16550 COM1 at I/O port 0x3f8.
 * ABI: cdecl; every runtime i64 is two stack words (low first) and an i64
 * result is returned in edx:eax. The image is linked at a fixed address, so
 * absolute addressing is fine (the stub allocates exactly that address). */
    .section .text.boot,"ax"
    .globl _start
_start:
    cli
    mov $bm_stack_top, %esp
    and $-16, %esp
    call __simple_main
    jmp bm_halt

    .text
    .globl bm_putc
bm_putc:
    mov $0x3fd, %dx
1:  in %dx, %al
    test $0x20, %al
    jz 1b
    mov $0x3f8, %dx
    mov 4(%esp), %al
    out %al, %dx
    ret

    .globl bm_load8
bm_load8:
    mov 4(%esp), %eax
    movzbl (%eax), %eax
    xor %edx, %edx
    ret

    .globl bm_store8
bm_store8:
    mov 4(%esp), %eax
    mov 12(%esp), %edx
    mov %dl, (%eax)
    ret

    .globl bm_halt
bm_halt:
    cli
1:  hlt
    jmp 1b

    .globl bm_arena_base
bm_arena_base:
    mov $bm_arena, %eax
    xor %edx, %edx
    ret

    .globl bm_arena_size
bm_arena_size:
    mov $65536, %eax
    xor %edx, %edx
    ret

    /* .data, not .bss: a flat image must carry the zeroed arena and stack. */
    .data
    .balign 16
bm_arena:
    .space 65536
bm_stack:
    .space 65536
bm_stack_top:
