# SimpleOS i686 user fixture: _start -> main (from the archive) -> exit via int 0x80.
	.text
	.globl _start
	.type _start, @function
_start:
	call main
	movl %eax, %ebx
	xorl %eax, %eax
	int $0x80
	.size _start, . - _start
