.text
.globl _main
.p2align 2
_main:
  bl _branch_target+4
  bl _branch_target+4
  adrp x0, (_data_target+4096)@PAGE
  add x0, x0, (_data_target+4096)@PAGEOFF
  adrp x1, (_data_target+16)@PAGE
  ldr x1, [x1, (_data_target+16)@PAGEOFF]
  ret
