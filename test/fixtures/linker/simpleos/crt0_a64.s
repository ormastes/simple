// Minimal SimpleOS-style aarch64 user crt0: a GLOBAL FUNC _start in .text
// that calls main and then parks. Mirrors the shape of the sysroot crt0.o.
    .text
    .globl _start
    .type _start, %function
_start:
    mov x29, #0
    bl main
1:
    b 1b
    .size _start, . - _start
