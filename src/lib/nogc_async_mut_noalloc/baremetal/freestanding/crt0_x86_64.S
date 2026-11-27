/* Freestanding crt0, x86_64 (long mode, entered from a UEFI loader stub).
 * Only what Simple cannot express: entry/stack switch, port I/O, byte
 * load/store, hlt. Everything else lives in bm_rt.spl.
 * Serial: 16550 COM1 at I/O port 0x3f8. Position independent (RIP-relative). */
    .section .text.boot,"ax"
    .globl _start
_start:
    cli
    lea bm_stack_top(%rip), %rsp
    and $-16, %rsp
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
    mov %dil, %al
    out %al, %dx
    ret

    .globl bm_load8
bm_load8:
    movzbq (%rdi), %rax
    ret

    .globl bm_store8
bm_store8:
    mov %sil, (%rdi)
    ret

    .globl bm_halt
bm_halt:
    cli
1:  hlt
    jmp 1b

    .globl bm_arena_base
bm_arena_base:
    lea bm_arena(%rip), %rax
    ret

    .globl bm_arena_size
bm_arena_size:
    mov $65536, %rax
    ret

    /* .data, not .bss: a flat image must carry the zeroed arena and stack. */
    .data
    .balign 16
bm_arena:
    .space 65536
bm_stack:
    .space 65536
bm_stack_top:
