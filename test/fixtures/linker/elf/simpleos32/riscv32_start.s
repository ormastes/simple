# SimpleOS riscv32 user fixture: _start -> main (from the archive) -> exit via ecall 0.
	.text
	.globl _start
	.type _start, @function
_start:
	call main
	li a7, 0
	ecall
	.size _start, . - _start
