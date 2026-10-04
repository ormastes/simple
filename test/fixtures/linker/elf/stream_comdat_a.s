.section .text.group,"axG",@progbits,local_signature,comdat
.local local_signature
local_signature:
.globl group_function
.type group_function,@function
group_function:
  mov $11,%eax
  ret
.section .rodata.group,"aG",@progbits,local_signature,comdat
.globl group_value
.type group_value,@object
group_value:
  .quad 11
.section .data.group,"awG",@progbits,local_signature,comdat
  .ascii "CDGROUPA"
  .quad group_value
