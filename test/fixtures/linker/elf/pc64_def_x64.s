.section .rodata,"a",@progbits
.globl pc64_target
.type pc64_target,@object
pc64_target:
  .byte 0x5a
.size pc64_target, . - pc64_target
