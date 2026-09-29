.section .data.target,"aw",@progbits
.globl pc_narrow_target
.type pc_narrow_target,@object
pc_narrow_target:
  .byte 0x6b
.size pc_narrow_target, . - pc_narrow_target
