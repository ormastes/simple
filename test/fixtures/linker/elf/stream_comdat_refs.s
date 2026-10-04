.text
.globl _start
_start:
  ret
.section .rodata
  .ascii "CDATROOT"
  .quad group_value
  .quad group_function
