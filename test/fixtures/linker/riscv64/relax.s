.option relax
.option rvc
.text
.globl _start
_start:
  call worker
  li a7, 93
  ecall
