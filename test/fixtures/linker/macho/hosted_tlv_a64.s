.text
.globl _main
.p2align 2
_main:
  stp x29, x30, [sp, #-16]!
  adrp x0, _tls@TLVPPAGE
  ldr x0, [x0, _tls@TLVPPAGEOFF]
  ldr x1, [x0]
  blr x1
  ldr w0, [x0]
  ldp x29, x30, [sp], #16
  ret
