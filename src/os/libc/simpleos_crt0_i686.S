/* SimpleOS i686 crt0: hand the entry stack to __simpleos_start32 (C). */
	.text
	.globl _start
	.type _start, @function
_start:
	xorl %ebp, %ebp
	movl %esp, %eax
	andl $-16, %esp
	subl $12, %esp
	pushl %eax
	call __simpleos_start32
	ud2
	.size _start, . - _start
