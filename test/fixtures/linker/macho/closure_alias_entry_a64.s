.text
.globl _main
.p2align 2
_main:
  adrp x1, _value@GOTPAGE
  ldr x1, [x1, _value@GOTPAGEOFF]
  b _alias
  ret
.data
.p2align 3
.globl _import_pointer
_import_pointer:
  .quad _value
  .quad _main
