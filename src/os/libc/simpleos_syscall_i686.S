/*
 * SimpleOS i686 user syscall: int64_t simpleos_syscall(int64_t id, a0..a4).
 * cdecl passes each int64_t as two stack words; the kernel takes the low
 * words in eax (id) and ebx, ecx, edx, esi, edi (args), see
 * src/os/kernel/arch/x86_32/trap_model.spl. Result is eax, sign-widened.
 */
	.text
	.globl simpleos_syscall
	.type simpleos_syscall, @function
simpleos_syscall:
	pushl %ebx
	pushl %esi
	pushl %edi
	movl 16(%esp), %eax
	movl 24(%esp), %ebx
	movl 32(%esp), %ecx
	movl 40(%esp), %edx
	movl 48(%esp), %esi
	movl 56(%esp), %edi
	int $0x80
	cltd
	popl %edi
	popl %esi
	popl %ebx
	ret
	.size simpleos_syscall, . - simpleos_syscall
