.include "tls_initial_exec.s"
.globl ie_ordinary
ie_ordinary:
  auipc a4, %got_pcrel_hi(ie_plain)
  ld a4, %pcrel_lo(ie_ordinary)(a4)
.data
.p2align 3
.globl ie_plain
.type ie_plain,@object
ie_plain:
  .quad 77
.size ie_plain, 8
