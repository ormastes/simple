#ifndef SIMPLEOS_WCHAR_H
#define SIMPLEOS_WCHAR_H

#include <stddef.h>

typedef int wchar_t;
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
