/*
 * SimpleOS syscall trampoline — x86_64 assembly
 *
 * ABI (from src/os/userlib/syscall_raw.spl):
 *   rax = syscall id
 *   rdi = arg0, rsi = arg1, rdx = arg2, r10 = arg3, r8 = arg4
 *   result returned in rax
 *
 * C calling convention input (System V AMD64):
 *   rdi = id, rsi = a0, rdx = a1, rcx = a2, r8 = a3, r9 = a4
 */

.section .text
.global simpleos_syscall
.type simpleos_syscall, @function

simpleos_syscall:
    /* Shuffle C calling convention args to syscall ABI */
    movq %rdi, %rax     /* id → rax */
    movq %rsi, %rdi     /* a0 → rdi */
    movq %rdx, %rsi     /* a1 → rsi */
    movq %rcx, %rdx     /* a2 → rdx */
    movq %r8,  %r10     /* a3 → r10 */
    movq %r9,  %r8      /* a4 → r8  */
    syscall
    ret

.size simpleos_syscall, . - simpleos_syscall
