.text
.globl _choice
.p2align 2
_choice:
  movl $22, %eax
  retq
.data
.p2align 3
.globl _value
_value:
  .quad 22
