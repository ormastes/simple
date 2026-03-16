/*
 * syscall_entry.S — SYSCALL/SYSRET entry for x86_64
 *
 * Part of the SimpleOS L4 microkernel (Simple language build).
 *
 * SYSCALL convention (System V AMD64 adapted for L4):
 *   RAX = syscall number
 *   RDI = arg0, RSI = arg1, RDX = arg2
 *   R10 = arg3 (RCX clobbered by SYSCALL)
 *   R8  = arg4, R9  = arg5
 *
 * On SYSCALL entry: RCX = user RIP, R11 = user RFLAGS
 */

.set MSR_STAR,      0xC0000081
.set MSR_LSTAR,     0xC0000082
.set MSR_SFMASK,    0xC0000084
.set MSR_EFER,      0xC0000080
.set SFMASK_VALUE,  0x200           /* Clear IF on entry */
.set TSS_RSP0_OFFSET, 4

/* ══════════════════════════════════════════════════════════════════════
 * syscall_init — Configure MSRs
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global syscall_init
.type   syscall_init, @function

syscall_init:
    /* Enable EFER.SCE */
    movl    $MSR_EFER, %ecx
    rdmsr
    orl     $1, %eax
    wrmsr

    /* STAR: kernel CS=0x08 in [47:32], user CS base=0x18 in [63:48] */
    movl    $MSR_STAR, %ecx
    xorl    %eax, %eax
    movl    $((0x18 << 16) | 0x08), %edx
    wrmsr

    /* LSTAR: syscall entry point */
    movl    $MSR_LSTAR, %ecx
    leaq    syscall_entry(%rip), %r8
    movq    %r8, %rax
    movl    %eax, %eax
    movq    %r8, %rdx
    shrq    $32, %rdx
    wrmsr

    /* SFMASK: clear IF */
    movl    $MSR_SFMASK, %ecx
    movl    $SFMASK_VALUE, %eax
    xorl    %edx, %edx
    wrmsr

    ret

.size syscall_init, . - syscall_init

/* ══════════════════════════════════════════════════════════════════════
 * syscall_entry — SYSCALL handler
 * ══════════════════════════════════════════════════════════════════════ */

.global syscall_entry
.type   syscall_entry, @function

.extern tss_block
.extern syscall_dispatch

syscall_entry:
    /* Save user RSP, load kernel stack from TSS RSP0 */
    movq    %rsp, %r12
    leaq    tss_block(%rip), %rsp
    movq    TSS_RSP0_OFFSET(%rsp), %rsp

    /* Save user context */
    pushq   %r12            /* User RSP */
    pushq   %r11            /* User RFLAGS */
    pushq   %rcx            /* User RIP */

    /* Save callee-saved registers */
    pushq   %rbp
    pushq   %rbx
    pushq   %r12
    pushq   %r13
    pushq   %r14
    pushq   %r15

    /* Prepare arguments for syscall_dispatch:
     * RDI = number (RAX), RSI = arg0 (RDI), RDX = arg1 (RSI),
     * RCX = arg2 (RDX), R8 = arg3 (R10), R9 = arg4 (R8) */
    movq    %rdi, %rsi      /* arg0 */
    movq    %rax, %rdi      /* syscall number */
    /* RDX = arg1 already */
    movq    %r10, %rcx      /* arg3 */
    /* R8  = arg4 already */
    /* R9  = arg5 already */

    call    syscall_dispatch

    /* RAX = return value */

    /* Restore callee-saved */
    popq    %r15
    popq    %r14
    popq    %r13
    popq    %r12
    popq    %rbx
    popq    %rbp

    /* Restore user context for SYSRET */
    popq    %rcx            /* User RIP */
    popq    %r11            /* User RFLAGS */
    popq    %rsp            /* User RSP */

    sysretq

.size syscall_entry, . - syscall_entry
