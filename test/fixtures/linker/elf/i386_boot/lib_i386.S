    .section .text, "ax"
    .globl lib_fn
lib_fn:
    movl $msg, %eax
    ret

    .section .rodata, "a"
msg:
    .asciz "hi"

    .section .data, "aw"
    .align 4
    .globl msg_ptr
msg_ptr:
    .long msg + 1
    .long lib_fn
    .globl counter
counter:
    .long 7
