/*
 * SimpleOS arm32 user syscall: int64_t simpleos_syscall(int64_t id, a0..a4).
 * AAPCS passes id in r0:r1 and a0 in r2:r3; a1..a4 go on the stack as 8-byte
 * aligned doublewords (low words at 0/8/16/24(sp)). The kernel takes id in r7
 * and args in r0..r4 (loader/arm32_real_exec_payload.spl: svc #0, r7 = id).
 * Result is r0, sign-widened into r1.
 */
	.text
	.arm
	.globl simpleos_syscall
	.type simpleos_syscall, %function
simpleos_syscall:
	push {r4, r7}
	mov r7, r0
	mov r0, r2
	ldr r1, [sp, #8]
	ldr r2, [sp, #16]
	ldr r3, [sp, #24]
	ldr r4, [sp, #32]
	svc #0
	asr r1, r0, #31
	pop {r4, r7}
	bx lr
	.size simpleos_syscall, . - simpleos_syscall
