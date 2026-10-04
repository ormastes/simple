.include "stream_got_inactive.s"
.section .rodata
  .ascii "GOTEMPTY"
  .quad _GLOBAL_OFFSET_TABLE_
base_only:
  .quad 0
  .reloc base_only, R_X86_64_GOTPC64, _GLOBAL_OFFSET_TABLE_
