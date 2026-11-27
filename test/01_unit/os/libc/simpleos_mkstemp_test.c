/*
 * Regression: runtime_native.c calls mkstemp() (process_run stderr capture),
 * and the SimpleOS libc neither declared nor defined it, so the aarch64 and
 * riscv64 sysroot cross-compiles of the runtime failed with an implicit
 * declaration error. mkstemp() must replace the trailing XXXXXX, open the
 * name with O_CREAT|O_EXCL, retry on EEXIST, and reject a bad template with
 * EINVAL without opening anything.
 */

#include <stdint.h>
#include "src/os/libc/include/errno.h"
#include "src/os/libc/include/fcntl.h"

typedef unsigned int useconds_t;

int errno = 0;
static int open_calls = 0;
static int open_flags_seen = 0;
static int eexist_budget = 0;
static char last_path[64];

int64_t simpleos_syscall(int64_t number, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4)
{
    (void)number; (void)a0; (void)a1; (void)a2; (void)a3; (void)a4;
    return 0;
}

int open(const char *path, int flags, ...)
{
    int i = 0;
    open_calls++;
    open_flags_seen = flags;
    while (path[i] && i < 63) { last_path[i] = path[i]; i++; }
    last_path[i] = 0;
    if (eexist_budget > 0) { eexist_budget--; errno = EEXIST; return -1; }
    return 7;
}

#include "src/os/libc/simpleos_fs.c"

static int has_x(const char *s) { for (; *s; s++) if (*s == 'X') return 1; return 0; }

int main(void)
{
    char t1[] = "/tmp/simple-XXXXXX";
    eexist_budget = 2;
    if (mkstemp(t1) != 7) return 1;
    if (open_calls != 3) return 2;
    if ((open_flags_seen & (O_CREAT | O_EXCL)) != (O_CREAT | O_EXCL)) return 3;
    if (has_x(t1 + 12)) return 4;
    for (int i = 0; t1[i]; i++) if (t1[i] != last_path[i]) return 5;

    char bad[] = "/tmp/short-XXX";
    open_calls = 0; errno = 0;
    if (mkstemp(bad) != -1) return 6;
    if (errno != EINVAL) return 7;
    if (open_calls != 0) return 8;
    return 0;
}
