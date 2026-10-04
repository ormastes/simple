.include "tls_initial_exec.s"
.globl ie_local_exec
ie_local_exec:
  lui a5, %tprel_hi(ie_tls_value)
  add a5, a5, tp, %tprel_add(ie_tls_value)
  ld a5, %tprel_lo(ie_tls_value)(a5)
