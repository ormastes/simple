    .section .text.boot, "ax"
    .globl _start
_start:
    movl val@GOTOFF(%ebx), %eax
    ret
    .section .data, "aw"
val:
    .long 1
