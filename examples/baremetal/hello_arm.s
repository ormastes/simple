# ARM Cortex-M3 Bare-Metal Hello World
# Vector table, UART output via Stellaris UART

.syntax unified
.cpu cortex-m3
.thumb

.section .vectors
.align 2
.global _vectors

_vectors:
    .word _stack_top              # Initial SP
    .word _start + 1              # Reset handler (+1 for Thumb)
    .word hang + 1                # NMI
    .word hang + 1                # HardFault
    .word hang + 1                # MemManage
    .word hang + 1                # BusFault
    .word hang + 1                # UsageFault
    .word 0, 0, 0, 0              # Reserved
    .word hang + 1                # SVCall
    .word hang + 1                # Debug
    .word 0                       # Reserved
    .word hang + 1                # PendSV
    .word hang + 1                # SysTick

.section .text
.thumb_func
.global _start

_start:
    # Write "Hello, ARM!" to UART0 (0x4000C000)
    ldr r0, =0x4000C000           # UART0 base
    ldr r1, =hello_msg
    mov r2, #11                   # Message length

write_loop:
    cmp r2, #0
    beq exit
    ldrb r3, [r1], #1             # Load byte, increment pointer
    str r3, [r0]                  # Write to UART DR
    subs r2, r2, #1
    b write_loop

exit:
    # Exit by writing to debug exit register (QEMU specific)
    ldr r0, =0xE0000000
    mov r1, #0x18                 # Exit code
    str r1, [r0]

hang:
    b hang

.section .rodata
hello_msg:
    .ascii "Hello, ARM!"

.section .bss
.align 3
_stack_bottom:
    .space 4096
_stack_top:
