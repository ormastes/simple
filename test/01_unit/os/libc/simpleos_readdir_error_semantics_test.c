/*
 * Regression: a failed directory-read syscall must remain distinguishable
 * from end-of-directory.  In particular, it must preserve retryability by
 * not latching DIR.eof.
 */

#include <stdint.h>
#include "src/os/libc/include/errno.h"

typedef unsigned int useconds_t;

int errno = 0;
static int readdir_calls = 0;

int64_t simpleos_syscall(int64_t number, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4)
{
    (void)a0;
    (void)a1;
    (void)a2;
    (void)a3;
    (void)a4;
    if (number != 36) return -1;
    readdir_calls++;
    return readdir_calls == 1 ? -EIO : 1;
}

#include "src/os/libc/simpleos_fs.c"

int main(void)
{
    struct _DIR_impl dir = { .fd = 7, .eof = 0 };

    errno = 0;
    if (readdir((DIR *)&dir) != NULL) return 1;
    if (errno != EIO) return 2;
    if (dir.eof != 0) return 3;
    if (readdir((DIR *)&dir) == NULL) return 4;
    if (readdir_calls != 2) return 5;
    return 0;
}
