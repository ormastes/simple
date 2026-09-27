.globl _start
.text
_start:
  .long target@GOT
  ret

.data
target:
  .quad 0x12345678
