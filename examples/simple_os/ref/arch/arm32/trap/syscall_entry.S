/*
 * syscall_entry.S — SVC (syscall) entry for ARM32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
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
 * to svc_handler in vectors.S, which saves context and calls handle_svc
 * in C. This file provides an alternative optimised fast-path entry.
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
     * Set up arguments for C syscall_dispatch:
     *   arg0 = syscall number (r7)
     *   arg1 = arg0 (r0, already saved on stack)
     *   arg2 = arg1 (r1)
     *   arg3 = arg2 (r2)
     *   arg4 = arg3 (r3)
     *   arg5 = arg4 (r4)
     *   arg6 = arg5 (r5)
     *
     * Rearrange: push extra args on stack, pass first 4 in r0-r3.
     */
    push    {r4, r5}           /* arg4, arg5 on stack */
    mov     r3, r3             /* arg3 = r3 (already there) */
    mov     r2, r2             /* arg2 = r2 (already there) */
    mov     r1, r1             /* arg1 = r1 (already there) */
    ldr     r0, [sp, #16]     /* arg0 = original r0 (from saved frame) */

    /* Push syscall number as first arg, shift others */
    /* Actually, re-arrange for: syscall_dispatch(number, a0, a1, a2, a3, a4, a5) */
    ldr     r0, [sp, #40]     /* r7 from saved frame = syscall number */
    ldr     r1, [sp, #8]      /* original r0 = arg0 */
    /* r2 = arg1 already in r2 from saved frame... */
    /* For simplicity, use the trap_handler path via handle_svc */

    bl      syscall_dispatch
    add     sp, sp, #8         /* Clean pushed r4, r5 */

    /*
     * Return value from syscall_dispatch is in r0.
     * Write it back into the saved r0 slot on the stack
     * so the caller sees it after we restore.
     */
    str     r0, [sp, #4]       /* Overwrite saved r0 */

    /* Restore SPSR */
    pop     {r8}
    msr     spsr_cxsf, r8

    /* Restore registers and return from exception */
    pop     {r0-r12, lr}
    movs    pc, lr              /* Return, restoring CPSR from SPSR */

.size syscall_entry_fast, . - syscall_entry_fast
