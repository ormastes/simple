.text
.p2align 2
  nop
.globl _branch_target
_branch_target:
  nop
  ret
.data
.p2align 12
  .quad 77
.globl _data_target
_data_target:
  .quad 88
  .space 4096
