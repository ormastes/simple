.globl _start
.data
target:
  .quad 7
.text
_start:
  .long 0
  ret
.reloc 0, R_X86_64_CODE_4_GOTPCRELX, target
