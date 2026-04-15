/* SimpleOS libc extensions — stubs/minimal impls to satisfy LLVM/rustc/
 * Simple-compiler cross-builds. Real implementations land as kernel
 * syscalls mature; until then these return ENOSYS or a reasonable
 * single-threaded noop. */

#include "simpleos_libc.h"
#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <time.h>
#include <locale.h>
#include <wchar.h>
#include <dlfcn.h>

/* ========== stdio extras ========== */
off_t ftello(FILE *f) { return (off_t)ftell(f); }
int fseeko(FILE *f, off_t off, int whence) { return fseek(f, (long)off, whence); }

/* ========== unistd: note — ftruncate lives in simpleos_fs.c as of Wave 4.
 *            DO NOT re-define here. */

/* ========== stdlib: realpath + putenv ========== */
char *realpath(const char *path, char *resolved) {
    if (!path) { errno = EINVAL; return NULL; }
    if (!resolved) {
        resolved = (char *)malloc(4096);
        if (!resolved) return NULL;
    }
    strncpy(resolved, path, 4095);
    resolved[4095] = '\0';
    return resolved;
}

int putenv(char *string) {
    if (!string) { errno = EINVAL; return -1; }
    char *eq = strchr(string, '=');
    if (!eq) return unsetenv(string);
    *eq = '\0';
    int rc = setenv(string, eq + 1, 1);
    *eq = '=';
    return rc;
}

/* ========== time: gmtime_r / localtime_r ========== */
struct tm *gmtime_r(const time_t *t, struct tm *result) {
    struct tm *g = gmtime(t);
    if (!g) return NULL;
    *result = *g;
    return result;
}

struct tm *localtime_r(const time_t *t, struct tm *result) {
    struct tm *l = localtime(t);
    if (!l) return NULL;
    *result = *l;
    return result;
}

/* ========== locale ========== */
static struct lconv _c_lconv = {
    ".", "", "", "", "", ".", "", "", "", "",
    127, 127, 127, 127, 127, 127, 127, 127,
};

char *setlocale(int category, const char *locale) {
    (void)category; (void)locale;
    return (char *)"C";
}

struct lconv *localeconv(void) { return &_c_lconv; }

/* ========== wide char ========== */
size_t wcslen(const wchar_t *s) {
    size_t n = 0;
    while (s[n]) n++;
    return n;
}

int wcscmp(const wchar_t *a, const wchar_t *b) {
    while (*a && *a == *b) { a++; b++; }
    return (*a < *b) ? -1 : (*a > *b) ? 1 : 0;
}

size_t mbstowcs(wchar_t *dst, const char *src, size_t n) {
    size_t i = 0;
    while (src[i] && i < n) {
        if (dst) dst[i] = (wchar_t)(unsigned char)src[i];
        i++;
    }
    if (dst && i < n) dst[i] = 0;
    return i;
}

size_t wcstombs(char *dst, const wchar_t *src, size_t n) {
    size_t i = 0;
    while (src[i] && i < n) {
        if (src[i] > 0x7F) { errno = EILSEQ; return (size_t)-1; }
        if (dst) dst[i] = (char)src[i];
        i++;
    }
    if (dst && i < n) dst[i] = 0;
    return i;
}

/* ========== dlfcn: all stub to NULL / ENOSYS ========== */
static char _dl_err[] = "dlopen: not supported on simpleos";
void *dlopen(const char *p, int m) { (void)p; (void)m; return NULL; }
void *dlsym(void *h, const char *n) { (void)h; (void)n; return NULL; }
int dlclose(void *h) { (void)h; return 0; }
char *dlerror(void) { return _dl_err; }

/* ========== fcntl: F_GETFD/F_SETFD/F_GETFL/F_SETFL are noop-success;
 *            F_DUPFD handled in simpleos_fs.c (already there via Wave 4). */
/* (ftruncate also lives in simpleos_fs.c — do NOT add here) */
