.option norelax
.option rvc
.text
.globl _start
_start:
.Lload:
  auipc t0, %pcrel_hi(data_value)
  lw a0, %pcrel_lo(.Lload)(t0)
.Lstore:
  auipc t2, %pcrel_hi(data_value)
  sw a0, %pcrel_lo(.Lstore)(t2)
  lui t3, %hi(data_value)
  lw a1, %lo(data_value)(t3)
  sw a1, %lo(data_value)(t3)
  call worker
  .reloc ., R_RISCV_BRANCH, fail_label
  .4byte 0x00050063
  jal zero, done_label
  lui t5, %hi(data_ptr)
.size _start, . - _start
.data
.globl data_ptr
.p2align 2
data_ptr:
  .4byte data_value
.size data_ptr, 4
