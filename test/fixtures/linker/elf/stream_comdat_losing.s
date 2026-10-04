.include "stream_comdat_b.s"
  .quad missing_group
losing_got:
  .quad 0
  .reloc losing_got, R_X86_64_GOTPCREL64, missing_group
.globl loser_only
loser_only:
  .quad 66
.local private_loser
private_loser:
  .quad 77
