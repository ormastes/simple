/*
 * syscall_entry.S — SVC #0 system call entry for AArch64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * AArch64 syscall calling convention (matching seL4 style):
 *   x8  = syscall number
 *   x0  = arg0
 *   x1  = arg1
 *   x2  = arg2
 *   x3  = arg3
 *   x4  = arg4
 *   x5  = arg5
 *
 * Return value placed in x0.
 *
 * Note: On AArch64, SVC causes a synchronous exception that is
 * handled through the vector table. The EC field in ESR_EL1 will
 * be 0x15 (SVC from AArch64). The SVC immediate value (#0) is
 * available in ESR_EL1 ISS bits [15:0].
 *
 * The actual SVC handling is done in trap_handler.c by reading
 * the syscall number from x8 in the trap frame. This file
 * provides the user-space SVC stub.
 */

.section .text
.global syscall_invoke
.type   syscall_invoke, @function

/*
 * uint64_t syscall_invoke(uint64_t number, uint64_t arg0,
 *                          uint64_t arg1, uint64_t arg2,
 *                          uint64_t arg3, uint64_t arg4);
 *
 * Arguments arrive in x0-x5 per AAPCS64.
 * We shuffle them to match our convention:
 *   x8 = number (from x0)
 *   x0 = arg0   (from x1)
 *   x1 = arg1   (from x2)
 *   x2 = arg2   (from x3)
 *   x3 = arg3   (from x4)
 *   x4 = arg4   (from x5)
 */
syscall_invoke:
    mov     x8, x0         /* syscall number */
    mov     x0, x1         /* arg0 */
    mov     x1, x2         /* arg1 */
    mov     x2, x3         /* arg2 */
    mov     x3, x4         /* arg3 */
    mov     x4, x5         /* arg4 */

    svc     #0

    /* Return value is in x0 after eret from kernel */
    ret

.size syscall_invoke, . - syscall_invoke
