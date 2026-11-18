# GOT reference with .data, an empty .init_array and .bss (SimpleOS user shape).
    .option pic
    .globl _start
    .text
_start:
    la a0, dvar
    ret
    .data
    .globl dvar
dvar: .quad 1
    .bss
bvar: .zero 64
