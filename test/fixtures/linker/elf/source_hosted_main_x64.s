.text
.globl main
.type main,@function
main:
  sub $8, %rsp
  mov $35, %edi
  call add_val
  add $8, %rsp
  ret
.size main, .-main
.section .note.GNU-stack,"",@progbits
