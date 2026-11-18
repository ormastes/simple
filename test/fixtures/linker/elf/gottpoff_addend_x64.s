# x86_64 GOTTPOFF with the usual -4 PC bias on a raw (unrelaxable) field.
# The GOT slot must hold tprel(tls_value) = -8, not tprel(tls_value - 4).
.globl _start
.text
_start:
  .long 0
  ret
.reloc 0, R_X86_64_GOTTPOFF, tls_value-4
.section .tdata,"awT",@progbits
.align 8
tls_value:
  .quad 7
