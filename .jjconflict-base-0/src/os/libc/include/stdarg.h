/*
 * SimpleOS <stdarg.h> — variable argument lists
 *
 * Forward to the compiler's built-in header. These macros are
 * compiler intrinsics and cannot be implemented in pure C.
 */

#ifndef _SIMPLEOS_STDARG_H
#define _SIMPLEOS_STDARG_H

#if defined(__has_include) && __has_include_next(<stdarg.h>)
#include_next <stdarg.h>
#else

/* Compiler built-in va_list support */
typedef __builtin_va_list va_list;

#define va_start(ap, param) __builtin_va_start(ap, param)
#define va_end(ap)          __builtin_va_end(ap)
#define va_arg(ap, type)    __builtin_va_arg(ap, type)
#define va_copy(dest, src)  __builtin_va_copy(dest, src)

#endif /* __has_include_next */

#endif /* _SIMPLEOS_STDARG_H */
