.globl _start
.text
_start:
  .long 0
  .long 0
  ret
.reloc 0, R_X86_64_CODE_4_GOTTPOFF, tls_value
.reloc 4, R_X86_64_CODE_6_GOTTPOFF, tls_value
.section .tdata,"awT",@progbits
.align 8
tls_value:
  .quad 7
