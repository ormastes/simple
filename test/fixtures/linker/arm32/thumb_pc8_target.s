.syntax unified
.thumb
.section .rodata.target,"a",%progbits
.balign 4
.global target
.type target,%object
target:
    .word 0x11223344
.size target, . - target
