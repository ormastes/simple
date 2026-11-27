// aarch64 boot fixture: CALL26/JUMP26, ADRP+ADD/LDST*_LO12, ABS64, PREL32.
    .section .text.entry, "ax"
    .globl _start
_start:
    adrp x0, _stack_top
    add  x0, x0, :lo12:_stack_top
    mov  sp, x0
    bl   lib_fn
    adrp x1, a64_bytes
    ldrb  w2, [x1, :lo12:a64_bytes]
    ldrh  w3, [x1, :lo12:a64_half]
    ldr   w4, [x1, :lo12:a64_word]
    ldr   x5, [x1, :lo12:a64_dword]
    ldr   q6, [x1, :lo12:a64_quad]
    b    lib_tail

    .section .text.vectors, "ax"
    .globl vectors
vectors:
    b    _start

    .section .simple.sandbox, "a"
    .quad 0x5a5a

    .section .data, "aw"
    .balign 16
a64_quad:
    .quad 0x1111, 0x2222
a64_dword:
    .quad lib_fn
a64_word:
    .word 7
    .word msg - .
a64_half:
    .hword 3
a64_bytes:
    .byte 9
    .balign 8
    .globl entry_ptr
entry_ptr:
    .quad _start + 8

    .section .bss, "aw", @nobits
    .balign 16
    .skip 64
