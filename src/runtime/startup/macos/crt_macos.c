/*
 * Simple Seed — macOS CRT (shared x86_64/arm64)
 *
 * macOS exit via syscall. XNU uses BSD syscall class (0x2000000)
 * on x86_64. On arm64, syscall numbers are direct (no class prefix).
 */

#include "../common/crt_common.h"

void __spl_exit(int status) {
#if defined(__x86_64__)
    __asm__ volatile (
        "mov $0x2000001, %%rax\n"  /* SYS_exit = 0x2000001 (BSD class) */
        "mov %0, %%edi\n"
        "syscall\n"
        :
        : "r" (status)
        : "rax", "rdi"
    );
#elif defined(__aarch64__)
    {
        register int x0 __asm__("x0") = status;
        __asm__ volatile (
            "mov x16, #1\n"        /* SYS_exit = 1 (arm64) */
            "svc #0x80\n"
            :
            : "r" (x0)
            : "x16"
        );
    }
#endif
    __builtin_unreachable();
}
