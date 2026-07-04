/*
 * SimpleOS Libc Shim -- C++ ABI support
 *
 * Provides the minimum C++ runtime symbols needed when linking code
 * compiled with clang++ -fno-exceptions -fno-rtti against this libc:
 *   - __dso_handle, __cxa_atexit, __cxa_finalize, atexit
 *   - __cxa_pure_virtual
 *   - __cxa_guard_acquire/release/abort  (function-local statics)
 *   - operator new / delete (mangled)
 *   - __libc_init_array  (.init_array support)
 *   - __stack_chk_guard / __stack_chk_fail
 *   - __assert_fail
 */

#include "include/stdlib.h"
#include "include/string.h"
#include "include/stdio.h"
#include "include/stdint.h"

/* ====================================================================
 * 1. DSO handle (required by __cxa_atexit)
 * ==================================================================== */

void *__dso_handle = 0;

/* ====================================================================
 * 2. atexit / __cxa_atexit / __cxa_finalize
 * ==================================================================== */

#define MAX_ATEXIT 128

static struct {
    void (*fn)(void *);
    void *arg;
    void *dso;
} _atexit_fns[MAX_ATEXIT];

static int _atexit_count = 0;

int __cxa_atexit(void (*destructor)(void *), void *arg, void *dso_handle) {
    if (_atexit_count >= MAX_ATEXIT) return -1;
    _atexit_fns[_atexit_count].fn  = destructor;
    _atexit_fns[_atexit_count].arg = arg;
    _atexit_fns[_atexit_count].dso = dso_handle;
    _atexit_count++;
    return 0;
}

void __cxa_finalize(void *dso_handle) {
    for (int i = _atexit_count - 1; i >= 0; i--) {
        if (!dso_handle || _atexit_fns[i].dso == dso_handle) {
            if (_atexit_fns[i].fn) {
                _atexit_fns[i].fn(_atexit_fns[i].arg);
                _atexit_fns[i].fn = (void (*)(void *))0;
            }
        }
    }
}

int atexit(void (*func)(void)) {
    return __cxa_atexit((void (*)(void *))func, (void *)0, (void *)0);
}

/* ====================================================================
 * 3. Pure virtual call handler
 * ==================================================================== */

void __cxa_pure_virtual(void) {
    /* Pure virtual function called -- abort */
    static const char msg[] = "pure virtual method called\n";
    write(2, msg, sizeof(msg) - 1);
    abort();
}

/* ====================================================================
 * 4. Function-local static guard variables (single-threaded)
 *
 * The guard is a 64-bit value. If the low byte is non-zero, the
 * variable is already initialized. __cxa_guard_acquire returns 1
 * if initialization is needed, 0 if already done.
 * ==================================================================== */

int __cxa_guard_acquire(long long *guard) {
    if (*(char *)guard) return 0; /* already initialized */
    return 1; /* needs initialization */
}

void __cxa_guard_release(long long *guard) {
    *(char *)guard = 1;
}

void __cxa_guard_abort(long long *guard) {
    *(char *)guard = 0;
}

/* ====================================================================
 * 5. operator new / delete (C++ mangled names)
 *
 * _Znwm  = operator new(size_t)
 * _Znam  = operator new[](size_t)
 * _ZdlPv = operator delete(void*)
 * _ZdaPv = operator delete[](void*)
 * _ZdlPvm = operator delete(void*, size_t)
 * _ZdaPvm = operator delete[](void*, size_t)
 * ==================================================================== */

void *_Znwm(unsigned long size) {
    void *p = malloc(size);
    if (!p) abort(); /* new must not return NULL (no exceptions) */
    return p;
}

void *_Znam(unsigned long size) {
    void *p = malloc(size);
    if (!p) abort();
    return p;
}

void _ZdlPv(void *ptr) {
    free(ptr);
}

void _ZdaPv(void *ptr) {
    free(ptr);
}

void _ZdlPvm(void *ptr, unsigned long size) {
    (void)size;
    free(ptr);
}

void _ZdaPvm(void *ptr, unsigned long size) {
    (void)size;
    free(ptr);
}

void *_ZnwmSt11align_val_t(unsigned long size, unsigned long align) {
    (void)align;
    return _Znwm(size);
}

void _ZdlPvmSt11align_val_t(void *ptr, unsigned long size, unsigned long align) {
    (void)size;
    (void)align;
    free(ptr);
}

void *_ZnwmRKSt9nothrow_t(unsigned long size, const void *tag) {
    (void)tag;
    return malloc(size);
}

void *_ZnamRKSt9nothrow_t(unsigned long size, const void *tag) {
    (void)tag;
    return malloc(size);
}

void _ZdlPvRKSt9nothrow_t(void *ptr, const void *tag) {
    (void)tag;
    free(ptr);
}

void _ZdaPvRKSt9nothrow_t(void *ptr, const void *tag) {
    (void)tag;
    free(ptr);
}

int __cxa_thread_atexit(void (*destructor)(void *), void *arg, void *dso_handle) {
    return __cxa_atexit(destructor, arg, dso_handle);
}

extern int _Z4mainiPPc(int, char **) __attribute__((weak));
extern int _Z4mainv(void) __attribute__((weak));

__attribute__((weak)) int main(int argc, char **argv) {
    if (_Z4mainiPPc) return _Z4mainiPPc(argc, argv);
    if (_Z4mainv) return _Z4mainv();
    return 0;
}

/* ====================================================================
 * 6. .init_array support -- called from CRT0 startup
 * ==================================================================== */

typedef void (*init_fn)(void);
extern init_fn __init_array_start[] __attribute__((weak));
extern init_fn __init_array_end[]   __attribute__((weak));
extern unsigned long simpleos_entropy_seed_u64(void) __attribute__((weak));
void __libc_init_array(void);

unsigned long __stack_chk_guard = 0;

static unsigned long simpleos_fallback_stack_seed(void) {
    unsigned long seed = (unsigned long)&__stack_chk_guard;
    seed ^= (unsigned long)&__libc_init_array;
    seed ^= (unsigned long)&simpleos_fallback_stack_seed;
    seed ^= 0x9E3779B9UL;
    seed ^= seed >> 33;
    seed *= 0x85EBCA6BUL;
    seed ^= seed >> 33;
    return seed ? seed : 0xA5A55A5AUL;
}

void __stack_chk_init(void) {
    unsigned long seed = 0;
    if (simpleos_entropy_seed_u64) {
        seed = simpleos_entropy_seed_u64();
    }
    if (!seed) {
        seed = simpleos_fallback_stack_seed();
    }
    __stack_chk_guard = seed;
}

void __libc_init_array(void) {
    __stack_chk_init();
    if (!__init_array_start || !__init_array_end) return;
    size_t count = (size_t)(__init_array_end - __init_array_start);
    for (size_t i = 0; i < count; i++) {
        if (__init_array_start[i]) {
            __init_array_start[i]();
        }
    }
}

/* ====================================================================
 * 7. Stack protection
 * ==================================================================== */

void __stack_chk_fail(void) {
    static const char msg[] = "*** stack smashing detected ***\n";
    write(2, msg, sizeof(msg) - 1);
    abort();
}

/* ====================================================================
 * 8. assert support
 * ==================================================================== */

void __assert_fail(const char *expr, const char *file,
                   unsigned int line, const char *func) {
    fprintf(stderr, "Assertion failed: %s at %s:%u (%s)\n",
            expr, file, line, func ? func : "?");
    abort();
}

/* ====================================================================
 * 9. _Exit -- immediate termination (no atexit, no flushing)
 * ==================================================================== */

extern int64_t simpleos_syscall(int64_t, int64_t, int64_t, int64_t,
                                 int64_t, int64_t);

static int running_on_linux_host(void) {
#if defined(__x86_64__)
    uint64_t cs;
    __asm__ volatile ("mov %%cs, %0" : "=r"(cs));
    return cs == 0x33;
#else
    return 0;
#endif
}

static int64_t linux_syscall1(int64_t id, int64_t a0) {
#if defined(__x86_64__)
    int64_t r;
    __asm__ volatile (
        "syscall"
        : "=a"(r)
        : "a"(id), "D"(a0)
        : "rcx", "r11", "memory");
    return r;
#else
    (void)id;
    (void)a0;
    return -38;
#endif
}

void _Exit(int status) {
    if (running_on_linux_host()) {
        linux_syscall1(60, (int64_t)status);
    }
    simpleos_syscall(0, (int64_t)status, 0, 0, 0, 0);
    __builtin_unreachable();
}
