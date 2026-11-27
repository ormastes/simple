@ SimpleOS arm32 user fixture: _start -> main (from the archive) -> exit via svc (r7 = 0).
	.text
	.arm
	.globl _start
	.type _start, %function
_start:
	bl main
	mov r7, #0
	svc #0
	.size _start, . - _start
