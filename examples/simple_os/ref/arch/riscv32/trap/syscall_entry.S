/*
 * syscall_entry.S — System call entry via ecall for RISC-V32
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * On RISC-V, system calls are triggered by the ecall instruction.
 * The trap handler in trap_handler.c dispatches ecalls based on mcause.
 *
 * Calling convention:
 *   a7 = syscall number
 *   a0 = arg0
 *   a1 = arg1
 *   a2 = arg2
 *   a3 = arg3
 *   a4 = arg4
 *   a5 = arg5
 *
 * Return value is placed in a0.
 *
 * Note: On RISC-V, ecall is handled as part of the normal trap path.
 * The trap_entry.S saves all registers, and trap_handler.c checks
 * mcause for ECALL_U (8) or ECALL_S (9) and dispatches accordingly.
 * This file provides a user-side ecall wrapper for completeness.
 */

.section .text
.global syscall
.type   syscall, @function

/*
 * uint32_t syscall(uint32_t number, uint32_t a0, uint32_t a1,
 *                  uint32_t a2, uint32_t a3, uint32_t a4);
 *
 * Arguments arrive in a0..a5 per the RISC-V calling convention:
 *   a0 = number (must be moved to a7)
 *   a1 = arg0   (must be moved to a0)
 *   a2 = arg1   (stays in a2 -> a1)
 *   a3 = arg2   (stays)
 *   a4 = arg3   (stays)
 *   a5 = arg4   (stays)
 */
syscall:
    /* Shuffle arguments: number -> a7, args shift down */
    mv      a7, a0          /* syscall number */
    mv      a0, a1          /* arg0 */
    mv      a1, a2          /* arg1 */
    mv      a2, a3          /* arg2 */
    mv      a3, a4          /* arg3 */
    mv      a4, a5          /* arg4 */

    ecall

    /* Return value is in a0 (set by trap handler) */
    ret

.size syscall, . - syscall
