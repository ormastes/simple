/* SimpleOS: strfmon — minimal ENOSYS stub. Monetary formatting is locale-heavy
 * and SimpleOS is fixed-UTF-8-C-locale. */
#include <errno.h>
#include <stddef.h>

#ifndef ENOSYS
#define ENOSYS 38
#endif

typedef long long ssize_t_t;

ssize_t_t strfmon(char *s, unsigned long maxsize, const char *format, ...) {
    (void)format;
    if (!s || maxsize == 0) { errno = ENOSYS; return -1; }
    s[0] = '\0';
    errno = ENOSYS;
    return -1;
}

ssize_t_t strfmon_l(char *s, unsigned long maxsize, void *locale, const char *format, ...) {
    (void)locale; (void)format;
    if (!s || maxsize == 0) { errno = ENOSYS; return -1; }
    s[0] = '\0';
    errno = ENOSYS;
    return -1;
}
