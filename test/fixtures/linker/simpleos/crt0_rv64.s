# Minimal SimpleOS-style riscv64 user crt0: a GLOBAL FUNC _start in .text
# that calls main and then parks. Mirrors the shape of the sysroot crt0.o.
    .text
    .globl _start
    .type _start, @function
_start:
    li s0, 0
    call main
1:
    j 1b
    .size _start, . - _start
