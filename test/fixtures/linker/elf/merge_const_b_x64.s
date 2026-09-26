.section .rodata.cst8,"aM",@progbits,8
.p2align 3
.Lconst_b:
    .quad 0x1122334455667788

.text
.globl const_b
.type const_b,@function
const_b:
    lea .Lconst_b(%rip), %rax
    ret
.size const_b, .-const_b
