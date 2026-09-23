    .section .text.entry, "ax", @progbits
    .globl _start
_start:
    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop
    la t0, _smp_online_count
    lw a0, 0(t0)
1:
    j 1b
