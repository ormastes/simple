.text
.globl _main
.p2align 2
_main:
  callq _choice
  movq _value@GOTPCREL(%rip), %rcx
  retq
.data
.p2align 3
.globl _chosen_pointer
_chosen_pointer:
  .quad _value
