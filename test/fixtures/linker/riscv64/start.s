.option norelax
.option rvc
.text
.globl _start
_start:
.Lload:
  auipc t0, %pcrel_hi(data_value)
  addi t1, zero, 1
  lw a0, %pcrel_lo(.Lload)(t0)
.Lstore:
  auipc t2, %pcrel_hi(data_value)
  sw a0, %pcrel_lo(.Lstore)(t2)
.Lgot:
  auipc t4, %got_pcrel_hi(data_value)
  ld t4, %pcrel_lo(.Lgot)(t4)
  lui t3, %hi(data_value)
  lw a1, %lo(data_value)(t3)
  sw a1, %lo(data_value)(t3)
  call worker
  .reloc ., R_RISCV_BRANCH, fail_label
  .4byte 0x00050063
  .reloc ., R_RISCV_RVC_BRANCH, fail_label
  .2byte 0xc101
  .reloc ., R_RISCV_RVC_JUMP, done_label
  .2byte 0xa001
  jal zero, fail_label
.size _start, . - _start
