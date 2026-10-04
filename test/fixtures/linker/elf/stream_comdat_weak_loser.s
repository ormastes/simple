.include "stream_comdat_b.s"
.weak weak_loser
.type weak_loser,@object
weak_loser:
  .quad 88
.size weak_loser,8
.section .rodata
  .ascii "CDWEAK!!"
  .quad weak_loser
weak_got:
  .quad 0
  .reloc weak_got, R_X86_64_GOTPCREL64, weak_loser
