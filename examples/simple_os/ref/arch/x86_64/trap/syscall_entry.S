/*
 * syscall_entry.S — SYSCALL/SYSRET entry for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * In x86_64, system calls use the SYSCALL instruction instead of int 0x80.
 * The SYSCALL instruction:
 *   - Loads RIP from LSTAR MSR
 *   - Saves old RIP in RCX
 *   - Saves old RFLAGS in R11
 *   - Masks RFLAGS with SFMASK MSR
 *   - Loads CS from STAR MSR bits 47:32
 *   - Loads SS from STAR MSR bits 47:32 + 8
 *   - Does NOT switch RSP — we must do it manually
 *
 * Calling convention (System V AMD64 adapted for L4):
 *   RAX = syscall number
 *   RDI = arg0
 *   RSI = arg1
 *   RDX = arg2
 *   R10 = arg3  (RCX is clobbered by SYSCALL)
 *   R8  = arg4
 *   R9  = arg5
 *
 * Return value in RAX.
 */

/* ── MSR addresses ─────────────────────────────────────────────────── */

.set MSR_STAR,      0xC0000081
.set MSR_LSTAR,     0xC0000082
.set MSR_SFMASK,    0xC0000084
.set MSR_EFER,      0xC0000080

/* Kernel segments: CS=0x08, SS=0x10
 * User segments:   CS=0x18|3=0x1B, SS=0x20|3=0x23
 * STAR[47:32] = kernel CS (0x08)
 * STAR[63:48] = user CS base (0x18) — CPU adds 16 for CS, 8 for SS
 * So STAR[63:48] should be 0x18 (user code = 0x18+16=0x1B+RPL, user data = 0x18+8=0x23) */
.set STAR_KERNEL_CS, 0x08
.set STAR_USER_CS,   0x18

/* SFMASK: clear IF (bit 9) on SYSCALL entry */
.set SFMASK_VALUE,  0x200

/* ══════════════════════════════════════════════════════════════════════
 * syscall_init — Configure MSRs for SYSCALL/SYSRET
 * Called once during kernel boot (from C).
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global syscall_init
.type   syscall_init, @function

syscall_init:
    /* Enable SCE (System Call Extensions) in EFER */
    movl    $MSR_EFER, %ecx
    rdmsr
    orl     $1, %eax            /* EFER.SCE = bit 0 */
    wrmsr

    /* Set STAR: kernel CS in bits 47:32, user CS base in bits 63:48 */
    movl    $MSR_STAR, %ecx
    xorl    %eax, %eax          /* Low 32 bits unused (EIP for compat mode) */
    movl    $((STAR_USER_CS << 16) | STAR_KERNEL_CS), %edx
    wrmsr

    /* Set LSTAR: 64-bit syscall entry point */
    movl    $MSR_LSTAR, %ecx
    leaq    syscall_entry(%rip), %rax
    movl    %eax, %eax          /* Zero-extend to clear upper EDX bits */
    movq    %rax, %rdx
    shrq    $32, %rdx
    /* EAX = low 32 bits, EDX = high 32 bits */
    leaq    syscall_entry(%rip), %rax
    movl    %eax, %eax
    leaq    syscall_entry(%rip), %r8
    movq    %r8, %rax
    movl    %eax, %eax          /* low 32 */
    movq    %r8, %rdx
    shrq    $32, %rdx           /* high 32 */
    wrmsr

    /* Set SFMASK: mask IF on syscall entry */
    movl    $MSR_SFMASK, %ecx
    movl    $SFMASK_VALUE, %eax
    xorl    %edx, %edx
    wrmsr

    ret

.size syscall_init, . - syscall_init

/* ══════════════════════════════════════════════════════════════════════
 * syscall_entry — SYSCALL handler entry point (loaded via LSTAR)
 *
 * On entry from SYSCALL:
 *   RCX = user RIP (return address)
 *   R11 = user RFLAGS
 *   RSP = still user stack (NOT switched!)
 *   CS  = kernel code selector (from STAR)
 *   SS  = kernel data selector (from STAR)
 *
 * We swap to the kernel stack from the TSS RSP0 field.
 * ══════════════════════════════════════════════════════════════════════ */

.global syscall_entry
.type   syscall_entry, @function

/* Offset of RSP0 in the TSS structure (after reserved0) */
.set TSS_RSP0_OFFSET, 4

.extern tss
.extern syscall_dispatch

syscall_entry:
    /* Interrupts are masked (SFMASK cleared IF).
     * RSP is still the user stack. */

    /* Save user RSP temporarily in a scratch register */
    movq    %rsp, %r12

    /* Load kernel stack from TSS RSP0 */
    movq    tss + TSS_RSP0_OFFSET(%rip), %rsp

    /* Build a syscall frame on the kernel stack */
    pushq   %r12            /* User RSP */
    pushq   %r11            /* User RFLAGS (saved by SYSCALL) */
    pushq   %rcx            /* User RIP (saved by SYSCALL) */

    /* Save callee-saved registers that we'll clobber */
    pushq   %rbp
    pushq   %rbx
    pushq   %r12
    pushq   %r13
    pushq   %r14
    pushq   %r15

    /* Move arg3 from R10 to RCX (System V ABI expects RCX for 4th arg,
     * but SYSCALL clobbered RCX with user RIP) */
    movq    %r10, %rcx

    /*
     * Call C dispatcher:
     *   syscall_dispatch(number, arg0, arg1, arg2, arg3, arg4, arg5)
     * Registers already set:
     *   RDI = arg0, RSI = arg1, RDX = arg2, RCX = arg3 (was R10)
     *   R8  = arg4, R9  = arg5
     * RAX = syscall number — push as first arg
     */
    /* Shuffle: move existing args to make room for syscall number as arg0 */
    movq    %r9, (%rsp)     /* Save R9 temporarily on stack (will be popped later) */
    pushq   %r8             /* arg4 on stack (7th arg) */
    pushq   %rcx            /* arg3 on stack (6th arg — R10 value) */

    /* Now call with:
     * RDI = syscall number (RAX), RSI = arg0 (old RDI), RDX = arg1 (old RSI),
     * RCX = arg2 (old RDX), R8 = arg3 (old R10), R9 = arg4 (old R8) */
    movq    %rdi, %rsi      /* arg0 -> RSI (2nd param) */
    movq    %rax, %rdi      /* syscall number -> RDI (1st param) */
    /* RDX = arg1, already in place as 3rd param */
    /* Move remaining args */
    movq    %r10, %rcx      /* arg3 -> RCX (4th param) */
    /* R8 = arg4 already in place as 5th param */
    /* R9 = arg5 already in place as 6th param */

    /* Clean up extra pushes */
    addq    $16, %rsp

    call    syscall_dispatch

    /* Return value is in RAX — will be returned to user */

    /* Restore callee-saved registers */
    popq    %r15
    popq    %r14
    popq    %r13
    popq    %r12
    popq    %rbx
    popq    %rbp

    /* Restore user RIP, RFLAGS, RSP for SYSRET */
    popq    %rcx            /* User RIP -> RCX */
    popq    %r11            /* User RFLAGS -> R11 */
    popq    %rsp            /* User RSP */

    /* Return to user mode */
    sysretq

.size syscall_entry, . - syscall_entry
