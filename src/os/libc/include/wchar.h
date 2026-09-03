#ifndef SIMPLEOS_WCHAR_H
#define SIMPLEOS_WCHAR_H

#include <stddef.h>

/* Use the compiler's own wchar_t so this typedef is identical to the one
 * <stddef.h> may already have provided (a C11 identical typedef redefinition
 * is legal; `int` vs the target's `unsigned int` is not). */
#ifdef __WCHAR_TYPE__
typedef __WCHAR_TYPE__ wchar_t;
#else
typedef int wchar_t;
#endif
typedef unsigned int wint_t;
#define WEOF ((wint_t)-1)

#ifdef __cplusplus
extern "C" {
#endif

size_t wcslen(const wchar_t *s);
int wcscmp(const wchar_t *a, const wchar_t *b);
size_t mbstowcs(wchar_t *dst, const char *src, size_t n);
size_t wcstombs(char *dst, const wchar_t *src, size_t n);

#ifdef __cplusplus
}
#endif
#endif
