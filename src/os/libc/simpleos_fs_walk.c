/* nftw/flock stubs. fnmatch is a real minimal impl (glob-style * and ?). */
#include <errno.h>
#include <string.h>

#ifndef ENOSYS
#define ENOSYS 38
#endif
#ifndef FNM_NOMATCH
#define FNM_NOMATCH 1
#endif

int nftw(const char *dirpath, int (*fn)(const char *, const void *, int, void *),
         int nopenfd, int flags) {
    (void)dirpath; (void)fn; (void)nopenfd; (void)flags;
    errno = ENOSYS; return -1;
}

int ftw(const char *dirpath, int (*fn)(const char *, const void *, int), int nopenfd) {
    (void)dirpath; (void)fn; (void)nopenfd;
    errno = ENOSYS; return -1;
}

int flock(int fd, int operation) {
    (void)fd; (void)operation;
    /* Single-process OS: no conflict possible — report success. */
    return 0;
}

/* Minimal fnmatch: only supports '*' (any run incl empty) and '?' (single char). */
int fnmatch(const char *pattern, const char *string, int flags) {
    (void)flags;
    if (!pattern || !string) return FNM_NOMATCH;
    while (*pattern) {
        if (*pattern == '*') {
            pattern++;
            if (!*pattern) return 0;
            while (*string) {
                if (fnmatch(pattern, string, 0) == 0) return 0;
                string++;
            }
            return FNM_NOMATCH;
        }
        if (*pattern == '?') {
            if (!*string) return FNM_NOMATCH;
        } else if (*pattern != *string) {
            return FNM_NOMATCH;
        }
        pattern++;
        string++;
    }
    return *string ? FNM_NOMATCH : 0;
}
