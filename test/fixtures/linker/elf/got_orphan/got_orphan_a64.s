// GOT reference with .data, an empty .init_array and .bss (SimpleOS user shape).
    .globl _start
    .text
_start:
    adrp x0, :got:dvar
    ldr x0, [x0, :got_lo12:dvar]
    ret
    .data
    .globl dvar
dvar: .quad 1
    .bss
bvar: .zero 64
