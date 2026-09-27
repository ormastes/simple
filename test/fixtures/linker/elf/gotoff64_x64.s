.globl _start
.data
value:
  .quad 0
.text
_start:
  .quad 0
  ret
.reloc 0, R_X86_64_GOTOFF64, value
