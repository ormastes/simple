.section .text
.globl _start
_start:
  li a0, 0
  li a1, 0x88000000
  li t0, 0x80200000
  csrw mepc, t0
  li t1, 0x00001800
  csrw mstatus, t1
  mret
