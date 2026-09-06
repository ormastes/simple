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

.global simpleos_current_cs
.type simpleos_current_cs, @function
simpleos_current_cs:
    xorl %eax, %eax
    movw %cs, %ax
    ret
.size simpleos_current_cs, . - simpleos_current_cs

.global simpleos_guest_arch_id
.type simpleos_guest_arch_id, @function
simpleos_guest_arch_id:
    movl $1, %eax
    ret
.size simpleos_guest_arch_id, . - simpleos_guest_arch_id

.global simpleos_user_context_ok
.type simpleos_user_context_ok, @function
simpleos_user_context_ok:
    xorl %eax, %eax
    movw %cs, %ax
    andl $3, %eax
    cmpl $3, %eax
    sete %al
    movzbl %al, %eax
    ret
.size simpleos_user_context_ok, . - simpleos_user_context_ok
