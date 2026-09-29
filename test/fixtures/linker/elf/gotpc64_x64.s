.globl _start
.text
_start:
  .quad 0
  ret
.reloc 0, R_X86_64_GOTPC64, _GLOBAL_OFFSET_TABLE_
