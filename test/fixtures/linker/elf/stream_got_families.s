.include "stream_got_refs.s"
  movq got_value@GOTPCREL(%rip), %r16
.section .rodata
  .ascii "GOTTABLE"
slot3:
  .long got_value@GOT
  .long 0
slot27:
  .quad got_value@GOT
slot30:
  .quad 0
  .reloc slot30, R_X86_64_GOTPLT64, got_function
base26:
  .long 0
  .long 0
  .reloc base26, R_X86_64_GOTPC32, _GLOBAL_OFFSET_TABLE_+5
base29:
  .quad 0
  .reloc base29, R_X86_64_GOTPC64, _GLOBAL_OFFSET_TABLE_+9
symbol25:
  .quad got_value@GOTOFF
symbol31:
  .quad got_function@PLTOFF
slot28:
  .quad 0
  .reloc slot28, R_X86_64_GOTPCREL64, got_value
anchor:
  .quad _GLOBAL_OFFSET_TABLE_
slot28_addend:
  .quad 0
  .reloc slot28_addend, R_X86_64_GOTPCREL64, got_value+7
.weak got_weak
weak_slot:
  .quad 0
  .reloc weak_slot, R_X86_64_GOTPCREL64, got_weak
common_slot:
  .quad 0
  .reloc common_slot, R_X86_64_GOTPCREL64, got_common
.comm got_common,24,32
alias_slot:
  .quad 0
  .reloc alias_slot, R_X86_64_GOTPCREL64, got_alias
