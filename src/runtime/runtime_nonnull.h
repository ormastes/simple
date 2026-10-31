/* runtime_nonnull.h: bridge for C pointer returns that must never be NULL.
 *
 * SIMPLE_RT_NONNULL(symbol, expr) evaluates expr exactly once, and if the
 * result is NULL it writes the symbol name to stderr and aborts. Use it only
 * where the sole cause of NULL is an allocation failure. Where NULL means a
 * caller-visible condition (invalid input, size limit), keep the NULL return.
 *
 * Header-only and C only (the macro yields void *). Portable to MSVC, GNU,
 * clang, FreeBSD and freestanding lanes that provide <stdio.h>/<stdlib.h>. */
#ifndef SIMPLE_RUNTIME_NONNULL_H
#define SIMPLE_RUNTIME_NONNULL_H

#include <stdio.h>
#include <stdlib.h>

#if defined(_MSC_VER)
#define SIMPLE_RT_NORETURN __declspec(noreturn)
#elif defined(__GNUC__) || defined(__clang__)
#define SIMPLE_RT_NORETURN __attribute__((noreturn))
#elif defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
#define SIMPLE_RT_NORETURN _Noreturn
#else
#define SIMPLE_RT_NORETURN
#endif

SIMPLE_RT_NORETURN static inline void simple_rt_null_violation(const char *symbol) {
    fputs("simple runtime: NULL from non-nil symbol: ", stderr);
    fputs(symbol ? symbol : "<unnamed>", stderr);
    fputs("\n", stderr);
    abort();
}

static inline void *simple_rt_nonnull_check(const char *symbol, void *p) {
    if (p == NULL) simple_rt_null_violation(symbol);
    return p;
}

#define SIMPLE_RT_NONNULL(symbol, expr) \
    simple_rt_nonnull_check((symbol), (void *)(expr))

#endif /* SIMPLE_RUNTIME_NONNULL_H */
