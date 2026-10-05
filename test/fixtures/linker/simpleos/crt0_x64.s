# Minimal SimpleOS-style x86_64 user crt0: a GLOBAL FUNC _start in .text
# that calls main and then parks. Mirrors the shape of the sysroot crt0.o.
    .text
    .globl _start
    .type _start, @function
_start:
    xorl %ebp, %ebp
    call main
    movl %eax, %edi
1:
    jmp 1b
    .size _start, . - _start
