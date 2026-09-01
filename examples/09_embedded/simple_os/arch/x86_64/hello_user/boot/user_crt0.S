.section .text._start
.global _start
_start:
    lea user_stack_top(%rip), %rsp
    call spl_start
    xor %edi, %edi
    mov $0, %rax
    syscall
1:  hlt
    jmp 1b
.section .bss
.balign 16
user_stack: .zero 65536
.global user_stack_top
user_stack_top:
