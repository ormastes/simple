/*
 * SimpleOS riscv32 user syscall: int64_t simpleos_syscall(int64_t id, a0..a4).
 * ILP32 passes each int64_t as a register pair (id a0:a1, a0 a2:a3, a1 a4:a5,
 * a2 a6:a7) and a3/a4 on the stack (low words at 0(sp) / 8(sp)). The kernel
 * takes id in a7 and args in a0..a4 (riscv32/user_entry_v1.spl, as rv64).
 * Result is a0, sign-widened into a1.
 */
	.text
	.globl simpleos_syscall
	.type simpleos_syscall, @function
simpleos_syscall:
	mv t0, a0
	mv a0, a2
	mv a1, a4
	mv a2, a6
	lw a3, 0(sp)
	lw a4, 8(sp)
	mv a7, t0
	ecall
	srai a1, a0, 31
	ret
	.size simpleos_syscall, . - simpleos_syscall
