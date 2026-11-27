# Use a clang build with the RISC-V target enabled:
# clang --target=riscv32-unknown-elf -march=rv32imac -mabi=ilp32 -c
#   riscv32_align.s -o riscv32_align.o
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
.section .data.align_refs,"aw",@progbits
.globl align_references
align_references:
  .word aligned_target
  .word second_target
  .word _start + 24
  .word .text + 24
