.globl _start
.globl abs16_target
.globl abs8_target
.text
_start:
  ret

.data
.globl abs_narrow_slots
abs_narrow_slots:
  .word abs16_target
  .byte abs8_target
