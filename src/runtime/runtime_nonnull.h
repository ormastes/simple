/* runtime_nonnull.h: bridge for C pointer returns that must never be NULL.
 *
 * SIMPLE_RT_NONNULL(symbol, expr) evaluates expr exactly once, and if the
 * result is NULL it aborts. Use it only where the sole cause of NULL is an
 * allocation failure. Where NULL means a caller-visible condition (invalid
 * input, size limit), keep the NULL return.
 *
 * Hosted builds (__STDC_HOSTED__ != 0, or MSVC) write the symbol name to
 * stderr and call abort(). Freestanding builds (__STDC_HOSTED__ == 0, which
 * -ffreestanding sets, or the repo's SIMPLE_RUNTIME_FREESTANDING_V2 marker)
 * include no <stdio.h> or
 * <stdlib.h>, cannot name the symbol, and fail by a trap instead, so the
 * header still compiles and links where no libc exists. Header-only, C only
 * (the macro yields void *). */
#ifndef SIMPLE_RUNTIME_NONNULL_H
#define SIMPLE_RUNTIME_NONNULL_H

#include <stddef.h> /* NULL: freestanding-safe, no stdio/stdlib */

#if (defined(__STDC_HOSTED__) && !__STDC_HOSTED__) || defined(SIMPLE_RUNTIME_FREESTANDING_V2)
#define SIMPLE_RT_FREESTANDING 1
#else
#define SIMPLE_RT_FREESTANDING 0
#endif

#if defined(_MSC_VER)
#define SIMPLE_RT_NORETURN __declspec(noreturn)
#elif defined(__GNUC__) || defined(__clang__)
#define SIMPLE_RT_NORETURN __attribute__((noreturn))
#elif defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
#define SIMPLE_RT_NORETURN _Noreturn
#else
#define SIMPLE_RT_NORETURN
#endif

#if SIMPLE_RT_FREESTANDING

/* No libc: no stdio, no stdlib, no abort(). Trap, never continue. */
SIMPLE_RT_NORETURN static inline void simple_rt_null_violation(const char *symbol) {
    (void)symbol;
#if defined(__GNUC__) || defined(__clang__)
    __builtin_trap();
#else
    for (;;) {
        *(volatile int *)0 = 0; /* fault: no trap intrinsic on this compiler */
    }
#endif
}

#else

#include <stdio.h>
#include <stdlib.h>

SIMPLE_RT_NORETURN static inline void simple_rt_null_violation(const char *symbol) {
    fputs("simple runtime: NULL from non-nil symbol: ", stderr);
    fputs(symbol ? symbol : "<unnamed>", stderr);
    fputs("\n", stderr);
    abort();
}

#endif

static inline void *simple_rt_nonnull_check(const char *symbol, void *p) {
    if (p == NULL) simple_rt_null_violation(symbol);
    return p;
}

#define SIMPLE_RT_NONNULL(symbol, expr) \
    simple_rt_nonnull_check((symbol), (void *)(expr))

#endif /* SIMPLE_RUNTIME_NONNULL_H */
