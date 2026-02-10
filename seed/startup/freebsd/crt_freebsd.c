/*
 * Simple Seed — FreeBSD CRT (shared x86/x86_64)
 *
 * FreeBSD exit via syscall. Same ELF ABI as Linux but different
 * syscall numbers and calling convention for i386.
 */

#include "../common/crt_common.h"

void __spl_exit(int status) {
#if defined(__x86_64__)
    __asm__ volatile (
        "mov $1, %%rax\n"    /* SYS_exit = 1 (FreeBSD x86_64) */
        "mov %0, %%edi\n"
        "syscall\n"
        :
        : "r" (status)
        : "rax", "rdi"
    );
#elif defined(__i386__)
    /* FreeBSD i386: syscall number in eax, args on stack */
    __asm__ volatile (
        "mov $1, %%eax\n"    /* SYS_exit = 1 (FreeBSD i386) */
        "push %0\n"
        "push $0\n"          /* dummy return address */
        "int $0x80\n"
        :
        : "r" (status)
        : "eax"
    );
#endif
    __builtin_unreachable();
}
