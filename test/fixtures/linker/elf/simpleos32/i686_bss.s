# __bss_start fixture: _start loads the weak __bss_start (as the SimpleOS C start does).
	.text
	.globl _start
	.weak __bss_start
_start:
	movl $__bss_start, %eax
	movl %eax, buf
	ret
	.bss
	.globl buf
	.p2align 2
buf:
	.zero 16
