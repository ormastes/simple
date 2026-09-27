.globl _start
.globl pc64_target
.text
_start:
  ret

.data
.globl pc64_slot
pc64_slot:
  .quad pc64_target - .
