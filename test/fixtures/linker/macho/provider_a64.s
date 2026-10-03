.text
.p2align 2
.globl _helper
_helper:
  mov w0, #42
  ret
.data
.p2align 3
.globl _value
_value:
  .quad 42
