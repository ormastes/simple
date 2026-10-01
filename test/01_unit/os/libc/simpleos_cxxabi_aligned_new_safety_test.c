#define malloc simpleos_test_malloc
#define free simpleos_test_free
#define calloc simpleos_test_calloc
#define realloc simpleos_test_realloc
#define main simpleos_cxxabi_guest_main
#define __dso_handle simpleos_cxxabi_test_dso_handle

#include <stddef.h>
#include <stdint.h>
#include <sys/wait.h>
#include <unistd.h>

int errno;

int64_t simpleos_syscall(int64_t number, int64_t a, int64_t b, int64_t c,
                         int64_t d, int64_t e)
{
    (void)number; (void)a; (void)b; (void)c; (void)d; (void)e;
    return -1;
}

#include "src/os/libc/simpleos_dlmalloc.c"
#include "src/os/libc/simpleos_cxxabi.c"

#undef main

int main(int argc, char **argv)
{
    (void)argc;
    (void)argv;
    void *ptr = _ZnwmSt11align_val_t(64U, 16U);
    if (!ptr || ((uintptr_t)ptr & 15U) != 0) return 1;
    _ZdlPvmSt11align_val_t(ptr, 64U, 16U);

    pid_t child = fork();
    if (child < 0) return 2;
    if (child == 0) {
        (void)_ZnwmSt11align_val_t(64U, 64U);
        return 3; /* over-aligned new must never return */
    }
    int status = 0;
    if (waitpid(child, &status, 0) != child) return 4;
    if (!WIFSIGNALED(status) && !(WIFEXITED(status) && WEXITSTATUS(status) != 0)) return 5;

    ptr = _ZnamSt11align_val_t(1U, 16U);
    if (!ptr || ((uintptr_t)ptr & 15U) != 0) return 6;
    _ZdaPvSt11align_val_t(ptr, 16U);

    ptr = _ZnwmSt11align_val_tRKSt9nothrow_t(1U, 16U, NULL);
    if (!ptr || ((uintptr_t)ptr & 15U) != 0) return 7;
    _ZdlPvSt11align_val_tRKSt9nothrow_t(ptr, 16U, NULL);
    if (_ZnamSt11align_val_tRKSt9nothrow_t(1U, 64U, NULL) != NULL) return 8;

    ptr = _ZnwmSt11align_val_t(1U, 16U);
    if (!ptr) return 9;
    _ZdlPvSt11align_val_t(ptr, 16U);
    ptr = _ZnamSt11align_val_t(1U, 16U);
    if (!ptr) return 10;
    _ZdaPvmSt11align_val_t(ptr, 1U, 16U);
    return 0;
}
