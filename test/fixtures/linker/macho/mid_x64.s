.text
.p2align 2
.globl _helper
_helper:
  jmp _leaf
.data
.p2align 3
.globl _value
_value:
  .quad 42
