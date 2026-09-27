.globl _start
.globl target
.text
_start:
  .quad 0
  ret
.reloc 0, R_X86_64_PLTOFF64, target
target:
  ret
