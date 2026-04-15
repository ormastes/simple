/*
 * syscall_entry.s — SimpleOS x86_64 SYSCALL kernel trampoline.
 *
 * Hardware state on SYSCALL entry (CPL=3 -> CPL=0):
 *   rcx = user RIP (saved by hardware)
 *   r11 = user RFLAGS (saved by hardware)
 *   rax = syscall number
 *   rdi, rsi, rdx, r10, r8, r9 = syscall args 0..5
 *     (NOTE: SYSCALL uses r10 instead of rcx for arg3 because rcx holds
 *      the saved user RIP.)
 *   CS loaded from MSR_STAR[47:32]  (kernel CS)
 *   SS loaded from MSR_STAR[47:32]+8
 *   IF cleared via MSR_SFMASK
 *
 * This trampoline is the C-callable bridge from the SYSCALL instruction
 * to the Simple-side kernel syscall dispatcher. It:
 *
 *   1. Swaps to a global kernel stack (SMP-unsafe but SimpleOS is single-
 *      CPU today; per-CPU GS-base scratch can be wired in later without
 *      changing the C-side ABI).
 *   2. Builds a struct syscall_regs on the kernel stack matching the
 *      C layout in baremetal_stubs.c.
 *   3. Calls rt_syscall_dispatch(regs*) which returns int64_t in rax.
 *   4. Restores user rcx/r11 and user rsp, then executes SYSRETQ.
 *
 * WARNING: this trampoline is NOT currently wired into MSR_LSTAR --
 * install_syscall_entry() remains a no-op until the GDT grows user
 * CS/SS entries and a C-ABI shim exists for the Simple-side syscall
 * handlers. The symbol is exported so cpu.spl can fetch its address
 * for a future wrmsr flip without another code change.
 *
 * Symbols exported:
 *   kernel_syscall_entry_asm      - the trampoline itself (goes in LSTAR)
 *   get_kernel_syscall_entry_addr - C-callable helper returning the
 *                                   address of the trampoline
 *
 * Symbols referenced (from baremetal_stubs.c):
 *   rt_syscall_dispatch           - C-side dispatcher
 *   _kernel_syscall_stack_top     - top of the global kernel stack
 *   _kernel_syscall_scratch_rsp   - scratch slot for user rsp
 */

    .section .text
    .globl kernel_syscall_entry_asm
    .type kernel_syscall_entry_asm, @function
    .align 16
kernel_syscall_entry_asm:
    /* Save user rsp and switch to the global kernel syscall stack.
     * Using a global stack is safe on single-CPU SimpleOS. When SMP
     * lands, replace with per-CPU GS-base scratch (see comment at top). */
    movq    %rsp, _kernel_syscall_scratch_rsp(%rip)
    movq    _kernel_syscall_stack_top(%rip), %rsp

    /* Build struct syscall_regs on the kernel stack.
     * Layout MUST match struct syscall_regs in baremetal_stubs.c.
     * Fields are pushed in reverse order (top of struct last). */
    pushq   $0x23           /* ss     - user SS (GDT user data | RPL3) */
    pushq   _kernel_syscall_scratch_rsp(%rip)  /* rsp - user rsp */
    pushq   %r11            /* rflags - user RFLAGS */
    pushq   $0x1B           /* cs     - user CS (GDT user code | RPL3) */
    pushq   %rcx            /* rip    - user RIP */
    pushq   $0              /* pad    - alignment filler */
    pushq   %rax            /* nr     - syscall number */
    pushq   %rdi            /* arg0 */
    pushq   %rsi            /* arg1 */
    pushq   %rdx            /* arg2 */
    pushq   %r10            /* arg3 (SYSCALL passes arg3 in r10) */
    pushq   %r8             /* arg4 */
    pushq   %r9             /* arg5 */

    /* Ensure 16-byte stack alignment for the System V call.
     * We pushed 13 * 8 = 104 bytes = 13 qwords, which leaves %rsp
     * 8-byte aligned but not 16-byte aligned for the callq. Align. */
    subq    $8, %rsp

    /* rdi = &regs (regs starts right after the alignment pad) */
    leaq    8(%rsp), %rdi
    call    rt_syscall_dispatch
    /* rax now holds the int64_t return value from the dispatcher. */

    /* Undo the alignment pad. */
    addq    $8, %rsp

    /* Tear down the struct. We do NOT restore rdi/rsi/rdx/r10/r8/r9
     * because the SYSCALL ABI does not require preserving them -- the
     * dispatcher owned them via the regs pointer. */
    addq    $48, %rsp       /* discard arg5..arg0 */
    addq    $8, %rsp        /* discard nr (rax already holds return value) */
    addq    $8, %rsp        /* discard pad */
    popq    %rcx            /* restore user RIP */
    addq    $8, %rsp        /* discard cs */
    popq    %r11            /* restore user RFLAGS */
    addq    $8, %rsp        /* discard user rsp slot */
    addq    $8, %rsp        /* discard user ss */

    /* Restore user rsp from scratch and return to user mode. */
    movq    _kernel_syscall_scratch_rsp(%rip), %rsp
    sysretq
    .size kernel_syscall_entry_asm, . - kernel_syscall_entry_asm

/* C-callable helper so Simple code can fetch the trampoline address
 * without needing raw symbol-to-u64 coercion. */
    .globl get_kernel_syscall_entry_addr
    .type get_kernel_syscall_entry_addr, @function
    .align 16
get_kernel_syscall_entry_addr:
    leaq    kernel_syscall_entry_asm(%rip), %rax
    ret
    .size get_kernel_syscall_entry_addr, . - get_kernel_syscall_entry_addr

/* Global kernel syscall stack (8 KiB). SMP-unsafe but single-CPU SimpleOS.
 * _kernel_syscall_stack_top (in .data) points at the high end. */
    .section .bss
    .align 16
    .globl _kernel_syscall_stack_base
_kernel_syscall_stack_base:
    .skip 8192
    .globl _kernel_syscall_stack_end
_kernel_syscall_stack_end:

    .align 8
    .globl _kernel_syscall_scratch_rsp
_kernel_syscall_scratch_rsp:
    .skip 8

    .section .data
    .align 8
    .globl _kernel_syscall_stack_top
_kernel_syscall_stack_top:
    .quad _kernel_syscall_stack_end

    .section .note.GNU-stack,"",@progbits
