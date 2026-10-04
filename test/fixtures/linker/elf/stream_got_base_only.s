.include "stream_got_inactive.s"
.section .rodata
  .ascii "GOTEMPTY"
base_only:
  .quad 0
  .reloc base_only, R_X86_64_GOTPC64, _GLOBAL_OFFSET_TABLE_
  .quad _start@PLTOFF
