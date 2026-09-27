.globl _start
.globl pc_narrow_target
.text
_start:
  ret

.section .data.slot,"aw",@progbits
.globl pc16_slot
pc16_slot:
  .word pc_narrow_target - .
.globl pc8_slot
pc8_slot:
  .byte pc_narrow_target - .
