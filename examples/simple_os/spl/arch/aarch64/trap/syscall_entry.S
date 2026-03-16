/*
 * syscall_entry.S — SVC #0 user-space stub for AArch64
 *
 * Part of the SimpleOS L4 microkernel (Simple language build).
 *
 * AArch64 syscall convention:
 *   x8  = syscall number
 *   x0  = arg0
 *   x1  = arg1
 *   x2  = arg2
 *   x3  = arg3
 *   x4  = arg4
 *   x5  = arg5
 *
 * Return value in x0 after eret.
 *
 * Note: The SVC instruction triggers a synchronous exception.
 * ESR_EL1 EC = 0x15 identifies it as an SVC from AArch64.
 * The kernel's trap_handler reads x8 from the saved trap frame.
 */

.section .text
.global syscall_invoke
.type   syscall_invoke, @function

/*
 * uint64_t syscall_invoke(uint64_t number, uint64_t arg0,
 *                          uint64_t arg1, uint64_t arg2,
 *                          uint64_t arg3, uint64_t arg4);
 *
 * AAPCS64: arguments in x0-x5
 * Remap to: x8=number, x0=arg0, x1=arg1, ...
 */
syscall_invoke:
    mov     x8, x0         /* syscall number */
    mov     x0, x1         /* arg0 */
    mov     x1, x2         /* arg1 */
    mov     x2, x3         /* arg2 */
    mov     x3, x4         /* arg3 */
    mov     x4, x5         /* arg4 */

    svc     #0

    ret

.size syscall_invoke, . - syscall_invoke
