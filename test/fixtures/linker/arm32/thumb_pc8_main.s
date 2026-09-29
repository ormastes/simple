.syntax unified
.thumb
.section .text.main,"ax",%progbits
.global main
.thumb_func
.type main,%function
main:
    .hword 0x4800
    .reloc main, R_ARM_THM_PC8, target
    bx lr
.size main, . - main

.extern target
