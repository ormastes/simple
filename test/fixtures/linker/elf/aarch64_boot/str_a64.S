// aarch64 SHF_MERGE|SHF_STRINGS fixture: ADRP+ADD into .rodata.str1.1 pieces.
    .section .text.entry, "ax"
    .globl _start
_start:
    adrp x0, .Lhello
    add  x0, x0, :lo12:.Lhello
    adrp x1, .Lworld
    add  x1, x1, :lo12:.Lworld
    b    _start

    .section .rodata.str1.1, "aMS", @progbits, 1
.Lhello:
    .asciz "hello"
.Lworld:
    .asciz "world!"
