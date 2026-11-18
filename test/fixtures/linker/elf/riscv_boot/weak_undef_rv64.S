# Calls, jumps and branches to an undefined weak symbol, linked above 4 GiB.
# ld.lld resolves each PC-relative form to the place itself (P), not to 0.
    .weak missing_fn
    .globl _start
    .section .text.boot,"ax",@progbits
_start:
    call missing_fn
    jal missing_fn
    beq a0, a1, missing_fn
    c.beqz a0, missing_fn
    c.j missing_fn
    ret
