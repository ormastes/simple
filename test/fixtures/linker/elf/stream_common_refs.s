.text
.globl _start
_start:
  ret
.section .rodata
  .ascii "COMTEST!"
  .byte 5
  .quad shared_common
  .quad shared_common
  .quad other_common
