/*
 * Simple Seed — Linux CRT (shared x86/x86_64)
 *
 * Linux exit via syscall. Works for both 32-bit and 64-bit
 * because we use the libc-free inline assembly approach.
 */

#include "../common/crt_common.h"

void __spl_exit(int status) {
#if defined(__x86_64__)
    __asm__ volatile (
        "mov $60, %%rax\n"   /* SYS_exit = 60 (x86_64) */
        "mov %0, %%edi\n"
        "syscall\n"
        :
        : "r" (status)
        : "rax", "rdi"
    );
#elif defined(__i386__)
    __asm__ volatile (
        "mov $1, %%eax\n"    /* SYS_exit = 1 (i386) */
        "mov %0, %%ebx\n"
        "int $0x80\n"
        :
        : "r" (status)
        : "eax", "ebx"
    );
#endif
    __builtin_unreachable();
}
