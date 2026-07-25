/* M-mode setup, then an S-mode load whose Sv39 physical target has no PMP match. */
.option norvc
.section .text
.globl _start
_start:
  li t0, 0x20000fff
  csrw pmpaddr0, t0
  li t0, 0x1f
  csrw pmpcfg0, t0
  la t0, trap
  csrw mtvec, t0
  li t0, 0x80001
  li t1, 8
  slli t1, t1, 60
  or t0, t0, t1
  csrw satp, t0
  sfence.vma x0, x0
  la t0, s_mode
  csrw mepc, t0
  li t0, 0x800
  csrw mstatus, t0
  mret

s_mode:
  lui t0, 0x40000
  ld a0, 0(t0)
  ebreak

trap:
  lui t0, 0x10000
  csrr t1, mcause
  sd t1, 0(t0)
  wfi
