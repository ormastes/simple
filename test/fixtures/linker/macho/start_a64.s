.text
.p2align 2
.globl _start
_start:
  bl _helper
  adrp x1, _value@PAGE
  ldr x0, [x1, _value@PAGEOFF]
  ret
