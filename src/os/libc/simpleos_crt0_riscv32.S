/* SimpleOS riscv32 crt0: hand the entry stack to __simpleos_start32 (C). */
	.text
	.globl _start
	.type _start, @function
_start:
	mv a0, sp
	andi sp, sp, -16
	call __simpleos_start32
	unimp
	.size _start, . - _start
