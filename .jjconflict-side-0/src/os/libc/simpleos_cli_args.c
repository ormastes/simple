/*
 * SimpleOS libc — Simple-runtime CLI argv bridge.
 *
 * These entry points hand argc/argv to the Simple language runtime, so they
 * reference Simple runtime symbols (rt_array_new / rt_array_push /
 * rt_array_len / rt_string_new) that only libsimple_runtime.a provides.
 *
 * They live in their own translation unit ON PURPOSE. Archive members are
 * pulled per-object, so keeping this block inside simpleos_libc.c dragged the
 * Simple runtime dependency into EVERY plain C/C++ link against
 * libsimpleos_c.a — including the CMake try-compile that configures the
 * cross LLVM build, which failed with `undefined symbol: rt_array_new` and
 * blocked the whole toolchain build. A C-only program never references these
 * symbols, so with them isolated here the linker never pulls this object.
 *
 * crt0.S takes a WEAK reference to rt_set_args, which does not pull an
 * archive member, so a C-only link stays clean.
 *
 * See doc/08_tracking/bug/simpleos_libc_leaks_simple_runtime_syms_2026-08-06.md
 */

#include <stddef.h>
#include <stdint.h>

extern size_t strlen(const char *s);

/* Canonical argv fallback for SimpleOS C-only programs.  Every symbol is weak:
 * when SimpleCore is linked its strong provider owns the same ABI and storage.
 * Keeping the aliases together prevents crt0 publication through rt_set_args
 * from being read back through an unrelated sys_get_args/rt_get_args store. */
static int64_t simpleos_cli_argc;
static int64_t simpleos_cli_argv;
extern int64_t rt_array_new(int64_t cap);
extern int8_t rt_array_push(int64_t array, int64_t value);
extern int64_t rt_array_len(int64_t array);
extern int64_t rt_string_new(int64_t bytes, int64_t len);

int64_t rt_array_len_safe(int64_t value) {
    if (value == 0 || value == 3) return 0;
    return rt_array_len(value);
}

__attribute__((weak)) void rt_set_args(int64_t argc, int64_t argv) {
    simpleos_cli_argc = argc;
    simpleos_cli_argv = argv;
}

__attribute__((weak)) void spl_init_args(int argc, char **argv) {
    rt_set_args((int64_t)argc, (int64_t)(uintptr_t)argv);
}

__attribute__((weak)) int64_t rt_cli_arg_count(void) {
    return simpleos_cli_argc;
}

__attribute__((weak)) int64_t rt_cli_arg_at(int64_t index) {
    char **argv = (char **)(uintptr_t)simpleos_cli_argv;
    if (index < 0 || index >= simpleos_cli_argc) {
        return rt_string_new(0, 0);
    }
    const char *arg = argv && argv[index] ? argv[index] : "";
    return rt_string_new((int64_t)(uintptr_t)arg, (int64_t)strlen(arg));
}

__attribute__((weak)) int64_t rt_cli_get_args(void) {
    char **argv = (char **)(uintptr_t)simpleos_cli_argv;
    int64_t args = rt_array_new(simpleos_cli_argc);
    for (int64_t i = 0; i < simpleos_cli_argc; i++) {
        const char *arg = argv && argv[i] ? argv[i] : "";
        rt_array_push(args, rt_string_new((int64_t)(uintptr_t)arg,
                                          (int64_t)strlen(arg)));
    }
    return args;
}

__attribute__((weak)) int64_t rt_get_args(void) {
    return rt_cli_get_args();
}

__attribute__((weak)) int64_t sys_get_args(void) {
    return rt_cli_get_args();
}
