/*
 * SimpleOS syscall trampoline — aarch64 assembly
 *
 * ABI (matches the arm64 EL1 sync vector in
 * examples/09_embedded/simple_os/arch/arm64/boot/crt0.S, EC=0x15):
 *   x8 = syscall id
 *   x0 = arg0, x1 = arg1, x2 = arg2, x3 = arg3, x4 = arg4
 *   result returned in x0
 *
 * C calling convention input (AAPCS64):
 *   x0 = id, x1 = a0, x2 = a1, x3 = a2, x4 = a3, x5 = a4
 */

.section .text
.global simpleos_syscall
.type simpleos_syscall, @function

simpleos_syscall:
    /* Shuffle C calling convention args to syscall ABI */
    mov     x8, x0      /* id  -> x8 */
    mov     x0, x1      /* a0  -> x0 */
    mov     x1, x2      /* a1  -> x1 */
    mov     x2, x3      /* a2  -> x2 */
    mov     x3, x4      /* a3  -> x3 */
    mov     x4, x5      /* a4  -> x4 */
    svc     #0
    ret

.size simpleos_syscall, . - simpleos_syscall

/*
 * simpleos_current_cs: x86 reports the CS selector (low 2 bits = CPL).
 * aarch64 EL0 cannot read CurrentEL; report the ring-3-equivalent constant
 * so callers checking `cs & 3 == 3` keep working.
 */
.global simpleos_current_cs
.type simpleos_current_cs, @function
simpleos_current_cs:
    mov     x0, #3
    ret
.size simpleos_current_cs, . - simpleos_current_cs
