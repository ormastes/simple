.globl _start
.text
_start:
  .long 0
  ret
.reloc 0, R_X86_64_GOTPC32, _GLOBAL_OFFSET_TABLE_
