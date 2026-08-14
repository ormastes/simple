/* Independent Sail RV32I ADD probe.  The checked opcode is 0x002081b3. */
.section .text
.globl _start
_start:
    addi x1, x0, 5
    addi x2, x0, 7
    add  x3, x1, x2
1:
    j 1b
