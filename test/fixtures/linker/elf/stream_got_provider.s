.data
.p2align 3
.globl got_value
.type got_value,@object
got_value:
  .quad 0x0102030405060708
.size got_value,8
.globl got_alias
.set got_alias, got_value
.text
.globl got_function
.type got_function,@function
got_function:
  ret
.size got_function,1
