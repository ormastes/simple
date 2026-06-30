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
