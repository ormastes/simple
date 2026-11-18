    .text
    .globl _start
_start:
    bl foo
    mov x8, #93
    svc #0
