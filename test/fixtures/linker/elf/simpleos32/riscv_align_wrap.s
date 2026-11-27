# Compile for both riscv32-unknown-elf / rv32imac / ilp32 and
# riscv64-unknown-elf / rv64imac / lp64. Undefined references intentionally
# include both GNU --wrap directions and an ALIGN rewrite between them.
.option relax
.option rvc
.text
.globl _start, __wrap_target
.type _start,@function
_start:
  call target
  c.nop
  .p2align 4
.type __wrap_target,@function
__wrap_target:
  call __real_target
  ret
.size __wrap_target, .-__wrap_target
.size _start, .-_start
