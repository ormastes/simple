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
#include <sys/stat.h>
#include <sys/mman.h>

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

int symlink(const char *target, const char *linkpath) {
    (void)target;
    (void)linkpath;
    errno = ENOSYS;
    return -1;
}

int link(const char *oldpath, const char *newpath) {
    (void)oldpath;
    (void)newpath;
    errno = ENOSYS;
    return -1;
}

ssize_t readlink(const char *path, char *buf, size_t bufsiz) {
    (void)path;
    (void)buf;
    (void)bufsiz;
    errno = ENOSYS;
    return -1;
}

int fchmod(int fd, mode_t mode) {
    (void)fd;
    (void)mode;
    errno = ENOSYS;
    return -1;
}

int fchown(int fd, uid_t owner, gid_t group) {
    (void)fd;
    (void)owner;
    (void)group;
    errno = ENOSYS;
    return -1;
}

mode_t umask(mode_t mask) {
    (void)mask;
    return 0;
}

int madvise(void *addr, size_t length, int advice) {
    (void)addr;
    (void)length;
    (void)advice;
    return 0;
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

locale_t uselocale(locale_t locale) {
    (void)locale;
    return LC_GLOBAL_LOCALE;
}

locale_t newlocale(int category_mask, const char *locale, locale_t base) {
    (void)category_mask;
    (void)locale;
    (void)base;
    return LC_GLOBAL_LOCALE;
}

void freelocale(locale_t locale) {
    (void)locale;
}

float strtof_l(const char *nptr, char **endptr, locale_t locale) {
    (void)locale;
    return strtof(nptr, endptr);
}

double strtod_l(const char *nptr, char **endptr, locale_t locale) {
    (void)locale;
    return strtod(nptr, endptr);
}

long double strtold(const char *nptr, char **endptr) {
    return (long double)strtod(nptr, endptr);
}

long double strtold_l(const char *nptr, char **endptr, locale_t locale) {
    (void)locale;
    return strtold(nptr, endptr);
}

long long strtoll_l(const char *nptr, char **endptr, int base, locale_t locale) {
    (void)locale;
    return strtoll(nptr, endptr, base);
}

unsigned long long strtoull_l(const char *nptr, char **endptr, int base,
                              locale_t locale) {
    (void)locale;
    return strtoull(nptr, endptr, base);
}

int strcoll(const char *s1, const char *s2) {
    return strcmp(s1, s2);
}

size_t strxfrm(char *dest, const char *src, size_t n) {
    size_t len = strlen(src);
    if (dest && n > 0) {
        size_t copy = len < n - 1 ? len : n - 1;
        memcpy(dest, src, copy);
        dest[copy] = '\0';
    }
    return len;
}

int strcoll_l(const char *s1, const char *s2, locale_t locale) {
    (void)locale;
    return strcoll(s1, s2);
}

size_t strxfrm_l(char *dest, const char *src, size_t n, locale_t locale) {
    (void)locale;
    return strxfrm(dest, src, n);
}

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

wchar_t *wcschr(const wchar_t *s, wchar_t c) {
    while (*s) {
        if (*s == c) return (wchar_t *)s;
        s++;
    }
    return c == 0 ? (wchar_t *)s : NULL;
}

wchar_t *wcsrchr(const wchar_t *s, wchar_t c) {
    const wchar_t *last = NULL;
    do {
        if (*s == c) last = s;
    } while (*s++);
    return (wchar_t *)last;
}

wchar_t *wcspbrk(const wchar_t *s, const wchar_t *accept) {
    for (; *s; s++) {
        for (const wchar_t *a = accept; *a; a++) {
            if (*s == *a) return (wchar_t *)s;
        }
    }
    return NULL;
}

wchar_t *wcsstr(const wchar_t *haystack, const wchar_t *needle) {
    if (!*needle) return (wchar_t *)haystack;
    for (; *haystack; haystack++) {
        const wchar_t *h = haystack;
        const wchar_t *n = needle;
        while (*h && *n && *h == *n) { h++; n++; }
        if (!*n) return (wchar_t *)haystack;
    }
    return NULL;
}

wchar_t *wmemchr(const wchar_t *s, wchar_t c, size_t n) {
    for (size_t i = 0; i < n; i++) {
        if (s[i] == c) return (wchar_t *)&s[i];
    }
    return NULL;
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

wint_t btowc(int c) {
    if (c == EOF) return WEOF;
    unsigned char ch = (unsigned char)c;
    return ch <= 0x7F ? (wint_t)ch : WEOF;
}

int wctob(wint_t c) {
    return c <= 0x7F ? (int)c : EOF;
}

size_t mbrtowc(wchar_t *pwc, const char *s, size_t n, mbstate_t *ps) {
    (void)ps;
    if (!s) return 0;
    if (n == 0) return (size_t)-2;
    unsigned char ch = (unsigned char)*s;
    if (ch == 0) {
        if (pwc) *pwc = 0;
        return 0;
    }
    if (ch > 0x7F) { errno = EILSEQ; return (size_t)-1; }
    if (pwc) *pwc = (wchar_t)ch;
    return 1;
}

size_t wcrtomb(char *s, wchar_t wc, mbstate_t *ps) {
    (void)ps;
    if (!s) return 1;
    if ((unsigned int)wc > 0x7F) { errno = EILSEQ; return (size_t)-1; }
    *s = (char)wc;
    return 1;
}

size_t mbsnrtowcs(wchar_t *dst, const char **src, size_t nms, size_t len,
                  mbstate_t *ps) {
    (void)ps;
    if (!src || !*src) return 0;
    const char *s = *src;
    size_t i = 0;
    while (i < len && i < nms && s[i]) {
        unsigned char ch = (unsigned char)s[i];
        if (ch > 0x7F) { errno = EILSEQ; return (size_t)-1; }
        if (dst) dst[i] = (wchar_t)ch;
        i++;
    }
    if (i < nms && s[i] == '\0') {
        if (dst && i < len) dst[i] = 0;
        *src = NULL;
    } else {
        *src = s + i;
    }
    return i;
}

size_t wcsnrtombs(char *dst, const wchar_t **src, size_t nwc, size_t len,
                  mbstate_t *ps) {
    (void)ps;
    if (!src || !*src) return 0;
    const wchar_t *s = *src;
    size_t i = 0;
    while (i < len && i < nwc && s[i]) {
        if ((unsigned int)s[i] > 0x7F) { errno = EILSEQ; return (size_t)-1; }
        if (dst) dst[i] = (char)s[i];
        i++;
    }
    if (i < nwc && s[i] == 0) {
        if (dst && i < len) dst[i] = '\0';
        *src = NULL;
    } else {
        *src = s + i;
    }
    return i;
}

static char *simpleos_wcs_to_ascii_alloc(const wchar_t *src) {
    size_t len = wcslen(src);
    char *buf = (char *)malloc(len + 1);
    if (!buf) return NULL;
    for (size_t i = 0; i < len; i++) {
        if ((unsigned int)src[i] > 0x7F) {
            free(buf);
            errno = EILSEQ;
            return NULL;
        }
        buf[i] = (char)src[i];
    }
    buf[len] = '\0';
    return buf;
}

static void simpleos_set_wide_end(const wchar_t *src, wchar_t **endptr,
                                  char *buf, char *narrow_end) {
    if (endptr) *endptr = (wchar_t *)(src + (narrow_end ? narrow_end - buf : 0));
}

double wcstod(const wchar_t *nptr, wchar_t **endptr) {
    char *buf = simpleos_wcs_to_ascii_alloc(nptr);
    if (!buf) { if (endptr) *endptr = (wchar_t *)nptr; return 0.0; }
    char *end = NULL;
    double value = strtod(buf, &end);
    simpleos_set_wide_end(nptr, endptr, buf, end);
    free(buf);
    return value;
}

float wcstof(const wchar_t *nptr, wchar_t **endptr) {
    char *buf = simpleos_wcs_to_ascii_alloc(nptr);
    if (!buf) { if (endptr) *endptr = (wchar_t *)nptr; return 0.0f; }
    char *end = NULL;
    float value = strtof(buf, &end);
    simpleos_set_wide_end(nptr, endptr, buf, end);
    free(buf);
    return value;
}

long double wcstold(const wchar_t *nptr, wchar_t **endptr) {
    char *buf = simpleos_wcs_to_ascii_alloc(nptr);
    if (!buf) { if (endptr) *endptr = (wchar_t *)nptr; return 0.0L; }
    char *end = NULL;
    long double value = strtold(buf, &end);
    simpleos_set_wide_end(nptr, endptr, buf, end);
    free(buf);
    return value;
}

long wcstol(const wchar_t *nptr, wchar_t **endptr, int base) {
    char *buf = simpleos_wcs_to_ascii_alloc(nptr);
    if (!buf) { if (endptr) *endptr = (wchar_t *)nptr; return 0; }
    char *end = NULL;
    long value = strtol(buf, &end, base);
    simpleos_set_wide_end(nptr, endptr, buf, end);
    free(buf);
    return value;
}

long long wcstoll(const wchar_t *nptr, wchar_t **endptr, int base) {
    char *buf = simpleos_wcs_to_ascii_alloc(nptr);
    if (!buf) { if (endptr) *endptr = (wchar_t *)nptr; return 0; }
    char *end = NULL;
    long long value = strtoll(buf, &end, base);
    simpleos_set_wide_end(nptr, endptr, buf, end);
    free(buf);
    return value;
}

unsigned long wcstoul(const wchar_t *nptr, wchar_t **endptr, int base) {
    char *buf = simpleos_wcs_to_ascii_alloc(nptr);
    if (!buf) { if (endptr) *endptr = (wchar_t *)nptr; return 0; }
    char *end = NULL;
    unsigned long value = strtoul(buf, &end, base);
    simpleos_set_wide_end(nptr, endptr, buf, end);
    free(buf);
    return value;
}

unsigned long long wcstoull(const wchar_t *nptr, wchar_t **endptr, int base) {
    char *buf = simpleos_wcs_to_ascii_alloc(nptr);
    if (!buf) { if (endptr) *endptr = (wchar_t *)nptr; return 0; }
    char *end = NULL;
    unsigned long long value = strtoull(buf, &end, base);
    simpleos_set_wide_end(nptr, endptr, buf, end);
    free(buf);
    return value;
}

int vswprintf(wchar_t *s, size_t n, const wchar_t *format, va_list ap) {
    char *fmt = simpleos_wcs_to_ascii_alloc(format);
    if (!fmt) return -1;
    char buf[1024];
    int rc = vsnprintf(buf, sizeof(buf), fmt, ap);
    free(fmt);
    if (rc < 0) return rc;
    size_t limit = n > 0 ? n - 1 : 0;
    size_t copy = (size_t)rc < limit ? (size_t)rc : limit;
    for (size_t i = 0; i < copy; i++) s[i] = (wchar_t)(unsigned char)buf[i];
    if (n > 0) s[copy] = 0;
    return rc;
}

int swprintf(wchar_t *s, size_t n, const wchar_t *format, ...) {
    va_list ap;
    va_start(ap, format);
    int rc = vswprintf(s, n, format, ap);
    va_end(ap);
    return rc;
}

int mbtowc(wchar_t *pwc, const char *s, size_t n) {
    size_t rc = mbrtowc(pwc, s, n, NULL);
    return rc == (size_t)-1 || rc == (size_t)-2 ? -1 : (int)rc;
}

size_t mbrlen(const char *s, size_t n, mbstate_t *ps) {
    return mbrtowc(NULL, s, n, ps);
}

size_t mbsrtowcs(wchar_t *dst, const char **src, size_t len, mbstate_t *ps) {
    if (!src || !*src) return 0;
    return mbsnrtowcs(dst, src, strlen(*src) + 1, len, ps);
}

int wcscoll(const wchar_t *s1, const wchar_t *s2) {
    return wcscmp(s1, s2);
}

size_t wcsxfrm(wchar_t *dest, const wchar_t *src, size_t n) {
    size_t len = wcslen(src);
    if (dest && n > 0) {
        size_t copy = len < n - 1 ? len : n - 1;
        for (size_t i = 0; i < copy; i++) dest[i] = src[i];
        dest[copy] = 0;
    }
    return len;
}

int wcscoll_l(const wchar_t *s1, const wchar_t *s2, locale_t locale) {
    (void)locale;
    return wcscoll(s1, s2);
}

size_t wcsxfrm_l(wchar_t *dest, const wchar_t *src, size_t n,
                 locale_t locale) {
    (void)locale;
    return wcsxfrm(dest, src, n);
}

size_t strftime_l(char *s, size_t max, const char *format, const struct tm *tm,
                  locale_t locale) {
    (void)locale;
    return strftime(s, max, format, tm);
}

int vasprintf(char **strp, const char *fmt, va_list ap) {
    if (!strp) { errno = EINVAL; return -1; }
    char *buf = (char *)malloc(4096);
    if (!buf) return -1;
    int n = vsnprintf(buf, 4096, fmt, ap);
    if (n < 0) { free(buf); return -1; }
    *strp = buf;
    return n;
}

int vsscanf(const char *str, const char *fmt, va_list ap) {
    (void)str;
    (void)fmt;
    (void)ap;
    return 0;
}

/* ========== dlfcn: libc self namespace + dynamic-loader syscall hooks ===== */

#define SIMPLEOS_SYS_DLOPEN  65
#define SIMPLEOS_SYS_DLSYM   66
#define SIMPLEOS_SYS_DLCLOSE 67
#define SIMPLEOS_DL_MAX_HANDLES 16
#define SIMPLEOS_DL_KIND_SELF 1
#define SIMPLEOS_DL_KIND_KERNEL 2

extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                int64_t a2, int64_t a3, int64_t a4);

typedef struct {
    int used;
    int kind;
    int refs;
    int64_t kernel_handle;
    char path[128];
} simpleos_dl_handle_t;

static simpleos_dl_handle_t _dl_main_handle = {
    1, SIMPLEOS_DL_KIND_SELF, 1, 0, "<main>"
};
static simpleos_dl_handle_t _dl_handles[SIMPLEOS_DL_MAX_HANDLES];
static char _dl_err[128];
static int _dl_has_error = 0;

static void _dl_clear_error(void) {
    _dl_has_error = 0;
    _dl_err[0] = '\0';
}

static void _dl_set_error(const char *msg, int err) {
    size_t n = 0;
    if (!msg) msg = "dynamic loader error";
    while (msg[n] && n < sizeof(_dl_err) - 1) {
        _dl_err[n] = msg[n];
        n++;
    }
    if (err > 0 && n + 16 < sizeof(_dl_err)) {
        const char suffix[] = ": errno ";
        size_t si = 0;
        while (suffix[si] && n < sizeof(_dl_err) - 1) {
            _dl_err[n++] = suffix[si++];
        }
        char digits[16];
        int di = 0;
        int v = err;
        if (v == 0) {
            digits[di++] = '0';
        } else {
            char tmp[16];
            int ti = 0;
            while (v > 0 && ti < 16) {
                tmp[ti++] = (char)('0' + (v % 10));
                v /= 10;
            }
            while (ti > 0) digits[di++] = tmp[--ti];
        }
        for (int i = 0; i < di && n < sizeof(_dl_err) - 1; i++) {
            _dl_err[n++] = digits[i];
        }
    }
    _dl_err[n] = '\0';
    _dl_has_error = 1;
}

static simpleos_dl_handle_t *_dl_find_path(const char *path) {
    for (int i = 0; i < SIMPLEOS_DL_MAX_HANDLES; i++) {
        if (_dl_handles[i].used && strcmp(_dl_handles[i].path, path) == 0) {
            return &_dl_handles[i];
        }
    }
    return NULL;
}

static simpleos_dl_handle_t *_dl_alloc_handle(void) {
    for (int i = 0; i < SIMPLEOS_DL_MAX_HANDLES; i++) {
        if (!_dl_handles[i].used) {
            memset(&_dl_handles[i], 0, sizeof(_dl_handles[i]));
            _dl_handles[i].used = 1;
            return &_dl_handles[i];
        }
    }
    return NULL;
}

static void *_dl_self_symbol(const char *name) {
    if (!name) return NULL;
    if (strcmp(name, "simpleos_syscall") == 0) return (void *)simpleos_syscall;
    if (strcmp(name, "malloc") == 0) return (void *)malloc;
    if (strcmp(name, "calloc") == 0) return (void *)calloc;
    if (strcmp(name, "realloc") == 0) return (void *)realloc;
    if (strcmp(name, "free") == 0) return (void *)free;
    if (strcmp(name, "open") == 0) return (void *)open;
    if (strcmp(name, "read") == 0) return (void *)read;
    if (strcmp(name, "write") == 0) return (void *)write;
    if (strcmp(name, "close") == 0) return (void *)close;
    if (strcmp(name, "lseek") == 0) return (void *)lseek;
    if (strcmp(name, "fork") == 0) return (void *)fork;
    if (strcmp(name, "execve") == 0) return (void *)execve;
    if (strcmp(name, "execv") == 0) return (void *)execv;
    if (strcmp(name, "execvp") == 0) return (void *)execvp;
    if (strcmp(name, "dlopen") == 0) return (void *)dlopen;
    if (strcmp(name, "dlsym") == 0) return (void *)dlsym;
    if (strcmp(name, "dlclose") == 0) return (void *)dlclose;
    if (strcmp(name, "dlerror") == 0) return (void *)dlerror;
    return NULL;
}

void *dlopen(const char *path, int mode) {
    _dl_clear_error();
    if (path == NULL) {
        _dl_main_handle.refs++;
        return &_dl_main_handle;
    }

    simpleos_dl_handle_t *existing = _dl_find_path(path);
    if (existing) {
        existing->refs++;
        return existing;
    }

    int64_t ret = simpleos_syscall(SIMPLEOS_SYS_DLOPEN,
        (int64_t)(uintptr_t)path, (int64_t)strlen(path), (int64_t)mode, 0, 0);
    if (ret < 0) {
        errno = (int)(-ret);
        _dl_set_error("dlopen failed", errno);
        return NULL;
    }

    simpleos_dl_handle_t *h = _dl_alloc_handle();
    if (!h) {
        simpleos_syscall(SIMPLEOS_SYS_DLCLOSE, ret, 0, 0, 0, 0);
        errno = ENOMEM;
        _dl_set_error("dlopen handle table full", errno);
        return NULL;
    }
    h->kind = SIMPLEOS_DL_KIND_KERNEL;
    h->refs = 1;
    h->kernel_handle = ret;
    strncpy(h->path, path, sizeof(h->path) - 1);
    h->path[sizeof(h->path) - 1] = '\0';
    return h;
}

void *dlsym(void *handle, const char *name) {
    _dl_clear_error();
    if (!name) {
        errno = EINVAL;
        _dl_set_error("dlsym name is null", errno);
        return NULL;
    }

    if (handle == RTLD_DEFAULT || handle == RTLD_NEXT ||
        handle == (void *)&_dl_main_handle) {
        void *sym = _dl_self_symbol(name);
        if (!sym) {
            errno = ENOENT;
            _dl_set_error("dlsym symbol not found", errno);
        }
        return sym;
    }

    simpleos_dl_handle_t *h = (simpleos_dl_handle_t *)handle;
    if (!h || !h->used || h->kind != SIMPLEOS_DL_KIND_KERNEL) {
        errno = EINVAL;
        _dl_set_error("dlsym invalid handle", errno);
        return NULL;
    }

    int64_t ret = simpleos_syscall(SIMPLEOS_SYS_DLSYM, h->kernel_handle,
        (int64_t)(uintptr_t)name, (int64_t)strlen(name), 0, 0);
    if (ret <= 0) {
        errno = ret < 0 ? (int)(-ret) : ENOENT;
        _dl_set_error("dlsym failed", errno);
        return NULL;
    }
    return (void *)(uintptr_t)ret;
}

int dlclose(void *handle) {
    _dl_clear_error();
    if (handle == RTLD_DEFAULT || handle == RTLD_NEXT ||
        handle == (void *)&_dl_main_handle) {
        return 0;
    }

    simpleos_dl_handle_t *h = (simpleos_dl_handle_t *)handle;
    if (!h || !h->used) {
        errno = EINVAL;
        _dl_set_error("dlclose invalid handle", errno);
        return -1;
    }

    if (h->refs > 1) {
        h->refs--;
        return 0;
    }

    if (h->kind == SIMPLEOS_DL_KIND_KERNEL) {
        int64_t ret = simpleos_syscall(SIMPLEOS_SYS_DLCLOSE,
            h->kernel_handle, 0, 0, 0, 0);
        if (ret < 0) {
            errno = (int)(-ret);
            _dl_set_error("dlclose failed", errno);
            return -1;
        }
    }
    memset(h, 0, sizeof(*h));
    return 0;
}

char *dlerror(void) {
    if (!_dl_has_error) return NULL;
    _dl_has_error = 0;
    return _dl_err;
}

/* ========== fcntl: F_GETFD/F_SETFD/F_GETFL/F_SETFL are noop-success;
 *            F_DUPFD handled in simpleos_fs.c (already there via Wave 4). */
/* (ftruncate also lives in simpleos_fs.c — do NOT add here) */
