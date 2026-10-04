.option norelax
.option norvc
.section .tdata,"awT",@progbits
.p2align 6
  .space 4096
.globl ie_tls_value
.type ie_tls_value,@tls_object
ie_tls_value:
  .quad 42
.size ie_tls_value, 8
.p2align 5
.globl ie_tls_second
.type ie_tls_second,@tls_object
ie_tls_second:
  .quad 99
.size ie_tls_second, 8
.section .tbss,"awT",@nobits
.p2align 6
.globl ie_tls_zero
.type ie_tls_zero,@tls_object
ie_tls_zero:
  .zero 8
.size ie_tls_zero, 8
