.globl _start
.text
_start:
  .quad target@GOT
  ret

.data
target:
  .byte 0x78
