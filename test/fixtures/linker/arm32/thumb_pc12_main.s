.syntax unified
.thumb
.section .text.main,"ax",%progbits
.global main
.thumb_func
.type main,%function
main:
    ldr r0, target
    bx lr
.size main, . - main

.extern target
