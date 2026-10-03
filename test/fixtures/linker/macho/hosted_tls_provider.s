.section __DATA,__thread_data,thread_local_regular
.p2align 3
_tls_initial:
  .quad 7
.section __DATA,__thread_vars,thread_local_variables
.globl _tls
.p2align 3
_tls:
  .quad __tlv_bootstrap
  .quad 0
  .quad _tls_initial
