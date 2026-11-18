/*
 * SimpleOS 32-bit C runtime start (i686, riscv32, arm32).
 *
 * Each arch's crt0 is only `_start: sp -> __simpleos_start32(sp)`; everything
 * the 64-bit crt0s do in assembly lives here once. Same contract as
 * simpleos_crt0_aarch64.S:
 *   sp[0] = argc (<= 64), argv = &sp[1] with every entry non-NULL and
 *   argv[argc] == NULL, envp after it terminating within 128 entries.
 * Malformed input exits 127 before any libc state is touched; a failed
 * __simple_startup_before_main exits 125.
 */
#include <stdint.h>

extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                int64_t a2, int64_t a3, int64_t a4);
extern int main(int argc, char **argv, char **envp);
extern void exit(int status) __attribute__((noreturn));
extern void __libc_init_array(void);
extern char **environ;

extern char __bss_start[] __attribute__((weak));
extern char __bss_end[] __attribute__((weak));
extern void rt_set_args(int argc, char **argv) __attribute__((weak));
extern int __simple_startup_before_main(int argc, char **argv) __attribute__((weak));
extern void __simple_call_module_inits(void) __attribute__((weak));

static void __attribute__((noreturn)) simpleos_start32_raw_exit(int status) {
    for (;;) simpleos_syscall(0, status, 0, 0, 0, 0);
}

void __attribute__((noreturn, used)) __simpleos_start32(uintptr_t *sp) {
    if (((uintptr_t)sp & 3) != 0) simpleos_start32_raw_exit(127);
    uintptr_t argc = sp[0];
    if (argc > 64) simpleos_start32_raw_exit(127);
    char **argv = (char **)(sp + 1);
    for (uintptr_t i = 0; i < argc; i++)
        if (argv[i] == 0) simpleos_start32_raw_exit(127);
    if (argv[argc] != 0) simpleos_start32_raw_exit(127);
    char **envp = argv + argc + 1;
    uintptr_t n = 0;
    while (envp[n] != 0) {
        if (++n > 128) simpleos_start32_raw_exit(127);
    }

    if (__bss_end && __bss_start < __bss_end) {
        for (volatile char *p = __bss_start; p < __bss_end; p++) *p = 0;
    }
    environ = envp;
    if (rt_set_args) rt_set_args((int)argc, argv);
    if (__simple_startup_before_main &&
        __simple_startup_before_main((int)argc, argv) != 0)
        simpleos_start32_raw_exit(125);
    __libc_init_array();
    if (__simple_call_module_inits) __simple_call_module_inits();
    exit(main((int)argc, argv, envp));
}
