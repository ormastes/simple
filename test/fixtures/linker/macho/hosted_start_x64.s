.text
.globl _main
.p2align 2
_main:
  pushq %rbp
  callq _helper
  movq _value@GOTPCREL(%rip), %rcx
  movq (%rcx), %rax
  popq %rbp
  retq
.data
.p2align 3
.globl _import_pointer
_import_pointer:
  .quad _value
  .quad _main
