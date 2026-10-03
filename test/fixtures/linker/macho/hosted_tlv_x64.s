.text
.globl _main
.p2align 2
_main:
  pushq %rbp
  movq _tls@TLVP(%rip), %rdi
  callq *(%rdi)
  movl (%rax), %eax
  popq %rbp
  retq
