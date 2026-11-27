    .section .text, "ax"
    .globl lib_fn
lib_fn:
    adrp x0, msg
    add  x0, x0, :lo12:msg
    ret
    .globl lib_tail
lib_tail:
    b    lib_tail

    .section .rodata, "a"
    .globl msg
msg:
    .asciz "hi"
