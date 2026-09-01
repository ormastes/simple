#include <stdint.h>

/* Guest libc owns errno as a plain global.  Rename it throughout the included
 * shim so this host fixture never binds to glibc's TLS errno. */
int simpleos_test_errno = 0;
#define errno simpleos_test_errno

int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4) {
    (void)id; (void)a0; (void)a1; (void)a2; (void)a3; (void)a4;
    return -38;
}

#define realpath simpleos_test_realpath
#include "src/os/libc/simpleos_libc_ext.c"

static int rejects(const char *path, char *resolved) {
    errno = 0;
    return simpleos_test_realpath(path, resolved) == NULL && errno == ENOSYS;
}

int main(void) {
    char output[4096];
    char oversized[4097];
    for (int i = 0; i < 4096; ++i) oversized[i] = 'x';
    oversized[4096] = '\0';

    if (!rejects("safe/../outside", output)) return 1;
    if (!rejects("relative/path", output)) return 2;
    if (!rejects("/missing/path", output)) return 3;
    if (!rejects(oversized, NULL)) return 4;
    if (!rejects(NULL, output)) return 5;
    return 0;
}
