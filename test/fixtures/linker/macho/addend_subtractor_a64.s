.text
.globl _main
.p2align 2
_main:
  ret
.data
.p2align 3
  .quad _data_target - _branch_target
