.section .rodata.cst8,"aM",@progbits,8
.p2align 3
.Lconst_a:
    .quad 0x1122334455667788

.text
.globl const_a
.type const_a,@function
const_a:
    lea .Lconst_a(%rip), %rax
    ret
.size const_a, .-const_a

.globl _start
.type _start,@function
_start:
    call const_a
    call const_b
    ret
.size _start, .-_start
