.text
.globl add_val
.type add_val,@function
add_val:
  mov base(%rip), %rax
  add %rdi, %rax
  ret
.size add_val, .-add_val
.section .rodata
.globl msg
msg:
  .asciz "hi\n"
.data
.p2align 3
.globl base
.type base,@object
base:
  .quad 7
.size base, 8
