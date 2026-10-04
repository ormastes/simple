.include "stream_got_inactive.s"
.local _GLOBAL_OFFSET_TABLE_
.data
.p2align 3
.type _GLOBAL_OFFSET_TABLE_,@object
_GLOBAL_OFFSET_TABLE_:
  .quad 77
.size _GLOBAL_OFFSET_TABLE_,8
.section .rodata
  .ascii "LOCALGOT"
local_anchor:
  .quad 0
  .reloc local_anchor, R_X86_64_64, _GLOBAL_OFFSET_TABLE_
