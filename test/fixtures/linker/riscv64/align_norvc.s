.option relax
.option norvc
.text
.globl _start, aligned_target
.type _start,@function
_start:
  call aligned_target
  nop
  .p2align 4
aligned_target:
  ret
.size _start, .-_start
