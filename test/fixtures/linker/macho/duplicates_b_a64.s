.text
.globl _choice
.p2align 2
_choice:
  mov w0, #22
  ret
.data
.p2align 3
.globl _value
_value:
  .quad 22
