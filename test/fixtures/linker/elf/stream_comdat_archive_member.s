.include "stream_comdat_b.s"
.data
.globl force_archive
force_archive:
  .quad 123
  .ascii "CDARCHIV"
