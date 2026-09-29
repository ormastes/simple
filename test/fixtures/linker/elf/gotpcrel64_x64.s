.globl _start
.text
_start:
  .quad 0
  ret
.reloc 0, R_X86_64_GOTPCREL64, target

.data
target:
  .byte 0x78
