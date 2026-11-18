/*
 * SimpleOS arm32 user entry: hand the initial sp (argc, argv..., envp...) to the
 * shared C start with an AAPCS 8-byte (here 16-byte) aligned stack.
 */
	.text
	.arm
	.globl _start
	.type _start, %function
_start:
	mov r0, sp
	bic sp, sp, #15
	bl __simpleos_start32
	udf #0
	.size _start, . - _start
