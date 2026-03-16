/*
 * syscall_entry.S — SVC (syscall) entry for ARM32
 *
 * Part of the SimpleOS L4 microkernel Simple language implementation.
 *
 * ARM32 L4-style syscall convention:
 *   r7 = syscall number
 *   r0 = arg0
 *   r1 = arg1
 *   r2 = arg2
 *   r3 = arg3
 *   r4 = arg4
 *   r5 = arg5
 *
 * Return value placed in r0.
 *
 * The SVC instruction causes an exception. The vector table dispatches
 * to svc_handler in vectors.S, which saves context and calls handle_svc.
 * This file provides an alternative optimised fast-path entry.
 */

.extern syscall_dispatch

.section .text
.global syscall_entry_fast
.type   syscall_entry_fast, %function

syscall_entry_fast:
    /*
     * On SVC entry:
     *   - CPU is in SVC mode
     *   - LR_svc = return address (instruction after SVC)
     *   - SPSR_svc = saved CPSR
     *   - r0-r7 contain syscall args and number
     */

    /* Save caller-saved registers and LR on the SVC stack */
    push    {r0-r12, lr}

    /* Save SPSR */
    mrs     r8, spsr
    push    {r8}

    /*
     * Set up arguments for syscall_dispatch:
     *   r0 = syscall number (from r7)
     *   r1 = arg0 (original r0, saved on stack)
     *   r2 = arg1 (original r1)
     *   r3 = arg2 (original r2)
     *   stack: arg3 (original r3), arg4 (r4), arg5 (r5)
     */
    push    {r3, r4, r5}       /* arg3, arg4, arg5 on stack */
    ldr     r3, [sp, #20]      /* arg2 = original r2 */
    ldr     r2, [sp, #16]      /* arg1 = original r1 */
    ldr     r1, [sp, #12]      /* arg0 = original r0 */
    mov     r0, r7             /* syscall number */

    bl      syscall_dispatch
    add     sp, sp, #12        /* Clean pushed r3, r4, r5 */

    /*
     * Return value from syscall_dispatch is in r0.
     * Write it back into the saved r0 slot.
     */
    str     r0, [sp, #4]       /* Overwrite saved r0 */

    /* Restore SPSR */
    pop     {r8}
    msr     spsr_cxsf, r8

    /* Restore registers and return from exception */
    pop     {r0-r12, lr}
    movs    pc, lr              /* Return, restoring CPSR from SPSR */

.size syscall_entry_fast, . - syscall_entry_fast
