.comm shared_common,4096,256
.data
  .ascii "BIGCOMMON!"
.globl trigger
trigger:
  .quad 123
