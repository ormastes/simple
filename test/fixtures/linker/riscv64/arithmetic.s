.option norelax
.text
.globl _start
_start:
  .quad arithmetic_values
.data
.globl arithmetic_values
arithmetic_values:
  .reloc ., R_RISCV_ADD8, delta_end
  .reloc ., R_RISCV_SUB8, delta_start
  .byte 1
  .reloc ., R_RISCV_ADD16, delta_end
  .reloc ., R_RISCV_SUB16, delta_start
  .half 2
  .reloc ., R_RISCV_ADD32, delta_end
  .reloc ., R_RISCV_SUB32, delta_start
  .word 3
  .reloc ., R_RISCV_ADD64, delta_end
  .reloc ., R_RISCV_SUB64, delta_start
  .quad 4
  .reloc ., R_RISCV_SET6, six_value
  .byte 0xc0
  .reloc ., R_RISCV_SUB6, two_value
  .byte 0xc9
  .reloc ., R_RISCV_SET8, byte_value
  .byte 0
  .reloc ., R_RISCV_SET16, half_value
  .half 0
  .reloc ., R_RISCV_SET32, word_value
  .word 0
  .reloc ., R_RISCV_32_PCREL, arithmetic_values
  .word 0
.globl delta_start, delta_end, six_value, two_value, byte_value, half_value, word_value
.set delta_start, 0x1000
.set delta_end, 0x1011
.set six_value, 5
.set two_value, 2
.set byte_value, 0xa5
.set half_value, 0xa55a
.set word_value, 0x76543210
