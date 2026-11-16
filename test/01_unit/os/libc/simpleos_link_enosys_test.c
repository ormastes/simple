/*
 * Regression: runtime_native.c calls link() (staged publish and the file
 * copy fast path), and the SimpleOS libc did not provide it, so the sysroot
 * cross-compile of the runtime broke.
 *
 * The SimpleOS kernel has no link syscall: its syscall table
 * (src/os/kernel/ipc/syscall.spl) has unlink (39) and rename (44) but no
 * link, and its mutable filesystem is FAT32, which has no hard links (stat
 * reports nlink == 1). So libc link() must fail honestly -- -1 with
 * errno == ENOSYS -- and must issue no syscall (a guessed number would reach
 * an unrelated handler). Callers already treat -1 as failure and fall back.
 */

#include <stdint.h>
#include "src/os/libc/include/errno.h"

typedef unsigned int useconds_t;

int errno = 0;
static int syscall_calls = 0;

int64_t simpleos_syscall(int64_t number, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4)
{
    (void)number;
    (void)a0;
    (void)a1;
    (void)a2;
    (void)a3;
    (void)a4;
    syscall_calls++;
    return 0;
}

#include "src/os/libc/simpleos_fs.c"

int main(void)
{
    errno = 0;
    if (link("/a", "/b") != -1) return 1;
    if (errno != ENOSYS) return 2;
    if (syscall_calls != 0) return 3;

    /* NULL paths: same honest failure, no dereference, no syscall. */
    errno = 0;
    if (link(NULL, NULL) != -1) return 4;
    if (errno != ENOSYS) return 5;
    if (syscall_calls != 0) return 6;
    return 0;
}
