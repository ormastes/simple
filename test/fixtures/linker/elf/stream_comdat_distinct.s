.section .text.distinct,"axG",@progbits,other_signature,comdat
.local other_signature
other_signature:
.globl distinct_function
.type distinct_function,@function
distinct_function:
  mov $33,%eax
  ret
.section .rodata.distinct,"aG",@progbits,other_signature,comdat
.globl distinct_value
.type distinct_value,@object
distinct_value:
  .quad 33
.section .data.distinct,"awG",@progbits,other_signature,comdat
  .ascii "CDOTHER!"
  .quad distinct_value
  .quad distinct_function
