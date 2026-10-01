/* One-shot ARM64 mounted-ELF acceptance payload.
 *
 * SimpleOS AArch64 syscall ABI:
 *   x8 = syscall number, x0..x4 = arguments
 * On entry x0/x1 name the kernel-staged read-only nonce line. DebugWrite (60)
 * writes that exact buffer; Exit (0) takes status in x0.
 */

.section .text
.global _start
.type _start, %function

_start:
    mov     x8, #60
    svc     #0

    mov     x0, #37
    mov     x8, #0
    svc     #0

1:
    wfe
    b       1b

.size _start, . - _start
