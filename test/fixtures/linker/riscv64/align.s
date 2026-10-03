.option relax
.option rvc
.text
.globl _start, aligned_target, second_target
.type _start,@function
_start:
  call aligned_target
  c.nop
  .p2align 4
aligned_target:
  addi a0, zero, 42
  .p2align 5
second_target:
  ret
.size _start, .-_start
.section .data.align_refs,"awR",@progbits
.globl align_references
align_references:
  .quad aligned_target
  .quad second_target
  .quad _start + 24
  .quad .text + 24
