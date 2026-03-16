/*
 * syscall_entry.S — System call entry via int 0x80 for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Calling convention (matching L4/seL4 style):
 *   EAX = syscall number
 *   EBX = arg0
 *   ECX = arg1
 *   EDX = arg2
 *   ESI = arg3
 *   EDI = arg4
 *
 * Return value is placed in the saved EAX slot of the trap frame
 * so the caller sees it in EAX after iret.
 */

.extern syscall_dispatch

.section .text
.global syscall_entry
.type   syscall_entry, @function

syscall_entry:
    cli

    /* Push dummy error code and interrupt number (0x80) */
    pushl   $0          /* error code (unused)  */
    pushl   $0x80       /* int_no = 128         */

    /* Save all general-purpose registers (pusha order) */
    pushal

    /* Save data segment */
    movw    %ds, %ax
    pushl   %eax

    /* Load kernel data segment */
    movw    $0x10, %ax
    movw    %ax, %ds
    movw    %ax, %es
    movw    %ax, %fs
    movw    %ax, %gs

    /*
     * Extract syscall arguments from the saved register state.
     * The trap frame on stack has the saved registers accessible
     * via the pushal order. We pass them as C arguments.
     *
     * C prototype:
     *   uint32_t syscall_dispatch(uint32_t number,
     *                             uint32_t arg0, uint32_t arg1,
     *                             uint32_t arg2, uint32_t arg3,
     *                             uint32_t arg4);
     *
     * We reconstruct from the saved frame. After pushal + push ds:
     *   [esp+ 0] = ds
     *   [esp+ 4] = edi    (arg4)
     *   [esp+ 8] = esi    (arg3)
     *   [esp+12] = ebp
     *   [esp+16] = _esp   (ignored)
     *   [esp+20] = ebx    (arg0)
     *   [esp+24] = edx    (arg2)
     *   [esp+28] = ecx    (arg1)
     *   [esp+32] = eax    (syscall number)
     */

    /* Push arguments right-to-left for cdecl */
    pushl   4(%esp)     /* arg4 = edi  (offset adjusted for each push) */
    pushl   12(%esp)    /* arg3 = esi  (original +8, +4 for prev push) */
    pushl   32(%esp)    /* arg2 = edx  (original +24, +8)              */
    pushl   40(%esp)    /* arg1 = ecx  (original +28, +12)             */
    pushl   36(%esp)    /* arg0 = ebx  (original +20, +16)             */
    pushl   52(%esp)    /* number = eax (original +32, +20)            */

    call    syscall_dispatch
    addl    $24, %esp   /* Clean 6 arguments */

    /*
     * Write return value (in EAX) back into the saved EAX slot
     * of the trap frame so the user process gets it after iret.
     * Saved EAX is at offset 32 from current ESP (after push ds + pusha).
     */
    movl    %eax, 32(%esp)

    /* Restore data segment */
    popl    %eax
    movw    %ax, %ds
    movw    %ax, %es
    movw    %ax, %fs
    movw    %ax, %gs

    /* Restore general-purpose registers */
    popal

    /* Remove int_no and error code */
    addl    $8, %esp

    /* Return to user mode */
    iret

.size syscall_entry, . - syscall_entry
