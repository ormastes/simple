.section .rodata
  .ascii "GOTLOCAL2"
local_slot:
  .quad 0
  .reloc local_slot, R_X86_64_GOTPCREL64, got_value
.data
.local got_value
.type got_value,@object
got_value:
  .quad 222
.size got_value,8
