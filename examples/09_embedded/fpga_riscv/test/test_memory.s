# Test memory load/store: store 77 to RAM, load it back, write to LED
# Expected: LED = 77

.section .text
.globl _start
_start:
    li   a0, 77
    li   a1, 0x100         # RAM address 0x100
    sw   a0, 0(a1)         # store 77
    lw   a2, 0(a1)         # load back
    lui  t0, 0x80000
    sw   a2, 0(t0)         # LED = 77
    ecall
