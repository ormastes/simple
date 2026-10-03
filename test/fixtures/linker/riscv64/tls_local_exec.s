.option norelax
.option norvc
.text
.globl _start
.type _start,@function
_start:
  lui a5, %tprel_hi(tls_value)
  add a5, a5, tp, %tprel_add(tls_value)
  lw a0, %tprel_lo(tls_value)(a5)
  sw a0, %tprel_lo(tls_zero)(a5)
  ret
.size _start, .-_start
.section .tdata,"awT",@progbits
.p2align 4
  .space 4096, 0
.globl tls_value
.type tls_value,@tls_object
tls_value:
  .word 42
.size tls_value, 4
.section .tbss,"awT",@nobits
.p2align 4
.globl tls_zero
.type tls_zero,@tls_object
tls_zero:
  .zero 4
.size tls_zero, 4
