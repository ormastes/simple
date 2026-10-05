.text
.globl _main
.p2align 2
_main:
  bl _choice
  adrp x1, _value@GOTPAGE
  ldr x1, [x1, _value@GOTPAGEOFF]
  ret
.data
.p2align 3
.globl _chosen_pointer
_chosen_pointer:
  .quad _value
