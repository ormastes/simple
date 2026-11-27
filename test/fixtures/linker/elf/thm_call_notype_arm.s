@ Thumb BL to a NOTYPE (non-STT_FUNC) Thumb label: no interworking (ld.lld keeps BL).
    .syntax unified
    .thumb
    .text
    .globl _start
    .type _start, %function
    .thumb_func
_start:
    bl tgt
    b .
