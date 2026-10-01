.globl _start
.text
_start:
  .long target@GOT
  ret

.data
target:
  .byte 0x78
