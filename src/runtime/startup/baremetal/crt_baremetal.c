/*
 * Simple Seed — Baremetal CRT (all architectures)
 *
 * No OS — halt the CPU after main returns.
 * Also provides __spl_start_bare which zeros BSS before
 * calling the common startup path.
 *
 * Supports: x86, x86_64, arm32, arm64, riscv32, riscv64
 */

#include "../common/crt_common.h"

void __spl_exit(int status) {
    (void)status;
#if defined(__x86_64__) || defined(__i386__)
    __asm__ volatile (
        "cli\n"
        "1: hlt\n"
        "jmp 1b\n"
    );
#elif defined(__aarch64__)
    __asm__ volatile (
        "msr daifset, #0xF\n"     /* Mask all exceptions */
        "1: wfi\n"
        "b 1b\n"
    );
#elif defined(__arm__)
    __asm__ volatile (
        "cpsid if\n"              /* Disable IRQ + FIQ */
        "1: wfi\n"
        "b 1b\n"
    );
#elif defined(__riscv)
    __asm__ volatile (
        "csrci mstatus, 0x8\n"   /* Clear MIE bit */
        "1: wfi\n"
        "j 1b\n"
    );
#else
    /* Generic fallback: infinite loop */
    for (;;) {}
#endif
    __builtin_unreachable();
}

/*
 * Baremetal entry — called from ASM after stack setup.
 * Zeros BSS (no OS loader to do it), then runs common startup.
 */
void __spl_start_bare(void) {
    __spl_zero_bss();

    /* Baremetal: no argc/argv/envp */
    __spl_start(0, (char **)0, (char **)0);
}
