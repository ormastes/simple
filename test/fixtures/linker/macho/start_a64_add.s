.text
.globl _start
.p2align 2
_start:
  bl _helper
  adrp x1, _value@PAGE
  add x0, x1, _value@PAGEOFF
  ret
