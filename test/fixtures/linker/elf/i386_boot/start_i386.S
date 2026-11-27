# i386 boot fixture: multiboot header, PC32/PLT32 calls, R_386_32 absolutes.
    .section .multiboot, "a"
    .align 4
    .long 0x1BADB002
    .long 0
    .long -0x1BADB002

    .section .text.boot, "ax"
    .globl _start
_start:
    movl $stack_top, %esp
    call lib_fn
    call lib_fn@PLT
    movl msg_ptr, %eax
    movl $counter, %ecx
    movl %eax, (%ecx)
1:  hlt
    jmp 1b

    .section .bss, "aw", @nobits
    .align 16
stack_bottom:
    .skip 64
    .globl stack_top
stack_top:
