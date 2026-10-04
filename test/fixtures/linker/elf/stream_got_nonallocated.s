.include "stream_got_unused_anchor.s"
.section .debug_info,"",@progbits
debug_field:
  .long 0
  .reloc debug_field, R_X86_64_GOTPCREL, _start
