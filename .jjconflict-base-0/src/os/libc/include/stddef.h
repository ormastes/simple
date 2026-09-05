/*
 * SimpleOS <stddef.h> — standard type definitions
 *
 * Forward to the compiler's built-in header if available,
 * otherwise provide explicit definitions.
 */

#ifndef _SIMPLEOS_STDDEF_H
#define _SIMPLEOS_STDDEF_H

#if defined(__has_include) && __has_include_next(<stddef.h>)
#include_next <stddef.h>
#else

typedef unsigned long size_t;
typedef long          ptrdiff_t;

#ifndef NULL
#ifdef __cplusplus
#define NULL nullptr
#else
#define NULL ((void *)0)
#endif
#endif

#define offsetof(type, member) __builtin_offsetof(type, member)

/* max_align_t — type with maximum fundamental alignment */
typedef struct {
    long long   __ll;
    long double __ld;
} max_align_t;

#endif /* __has_include_next */

#endif /* _SIMPLEOS_STDDEF_H */
