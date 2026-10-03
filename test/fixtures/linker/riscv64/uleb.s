.option norelax
.text
.globl _start, end_marker
_start:
  .quad uleb_values
  .space 128, 0
end_marker:
  nop
.data
.globl uleb_values
uleb_values:
  .reloc ., R_RISCV_SET_ULEB128, end_marker
  .reloc ., R_RISCV_SUB_ULEB128, _start
  .byte 0x80, 0x80, 0
  .reloc ., R_RISCV_SET_ULEB128, thirteen
  .reloc ., R_RISCV_SUB_ULEB128, zero_value
  .byte 0
.set thirteen, 13
.set zero_value, 0
