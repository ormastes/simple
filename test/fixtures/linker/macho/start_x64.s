.text
.p2align 2
.globl _start
_start:
  callq _helper
  retq
.data
.p2align 3
.globl _pointer
_pointer:
  .quad _value
