/* Minimal Cortex-M semihost smoke fixture shared by OpenOCD and TRACE32. */

.syntax unified
.cpu cortex-m4
.thumb

.section .isr_vector, "a", %progbits
.word _stack_top
.word _start + 1

.section .text._start, "ax", %progbits
.global _start
.type _start, %function
_start:
    ldr r0, =message
1:
    ldrb r1, [r0], #1
    cbz r1, 2f
    movs r0, #3
    bkpt 0xAB
    b 1b
2:
    movs r0, #24
    movs r1, #0
    bkpt 0xAB
3:
    b 3b

.size _start, . - _start

.section .rodata, "a", %progbits
message:
    .asciz "simple-stm-smoke\n"

.section .stack, "aw", %progbits
.space 1024
_stack_top:
