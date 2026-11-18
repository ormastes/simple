@ tgt is NOTYPE, so its value carries no Thumb bit.
    .syntax unified
    .thumb
    .text
    .globl tgt
tgt:
    bx lr
