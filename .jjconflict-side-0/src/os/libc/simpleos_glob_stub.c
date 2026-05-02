#include <errno.h>
#ifndef ENOSYS
#define ENOSYS 38
#endif

typedef struct { unsigned long gl_pathc; char **gl_pathv; unsigned long gl_offs; } glob_t;

int glob(const char *pattern, int flags, int (*errfunc)(const char *, int), glob_t *pglob) {
    (void)pattern; (void)flags; (void)errfunc;
    if (pglob) { pglob->gl_pathc = 0; pglob->gl_pathv = 0; pglob->gl_offs = 0; }
    errno = ENOSYS;
    return 2;  /* GLOB_ABORTED */
}

void globfree(glob_t *pglob) {
    (void)pglob;
}

int wordexp(const char *s, void *p, int flags) {
    (void)s; (void)p; (void)flags;
    errno = ENOSYS; return -1;
}

void wordfree(void *p) { (void)p; }
