/* Freestanding crt0, i686 (IA32 protected mode, entered from a UEFI IA32 loader stub).
 * Only what Simple cannot express: entry/stack switch, port I/O, byte
 * load/store, hlt. Everything else lives in bm_rt32.spl.
 * Serial: 16550 COM1 at I/O port 0x3f8.
 * ABI: cdecl with bm_rt32.spl widths: every runtime argument is one 32-bit
 * stack word (pointers, bytes, bm_store8 value). Position independent: the loader stub copies
 * the image wherever AllocatePages(AnyPages) put it, so data is reached via
 * GOTPC/GOTOFF (the GOT is only an anchor; no GOT slots are used). */
    .section .text.boot,"ax"
    .globl _start
_start:
    cli
    call 1f
1:  pop %eax
    addl $_GLOBAL_OFFSET_TABLE_+(.-1b), %eax
    lea bm_stack_top@GOTOFF(%eax), %esp
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
    mov 8(%esp), %edx         /* value: 32-bit arg (bm_rt32.spl ABI) */
    mov %dl, (%eax)
    ret

    .globl bm_halt
bm_halt:
    cli
1:  hlt
    jmp 1b

    .globl bm_arena_base
bm_arena_base:
    call 2f
2:  pop %eax
    addl $_GLOBAL_OFFSET_TABLE_+(.-2b), %eax
    lea bm_arena@GOTOFF(%eax), %eax
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
