.text
.p2align 2
.globl _helper
_helper:
  movl $42, %eax
  retq
.data
.p2align 3
.globl _value
_value:
  .quad 42
