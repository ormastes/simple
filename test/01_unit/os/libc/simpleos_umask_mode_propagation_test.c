/* Regression: guest creation must fail closed until SimpleOS persists and
 * enforces umask-restricted permissions. */

#include <stdint.h>
#include "src/os/libc/include/fcntl.h"
#include "src/os/libc/include/sys/stat.h"
#include "src/os/libc/include/errno.h"

static int open_calls = 0;
static int mkdir_calls = 0;

int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4)
{
    (void)a0;
    (void)a1;
    (void)a2;
    (void)a3;
    (void)a4;
    if (id == 4) return 0; /* guest path */
    if (id == 30) {
        open_calls++;
        return 7;
    }
    if (id == 35) {
        mkdir_calls++;
        return 0;
    }
    return -38;
}

int main(void)
{
    if (umask(077) != 022) return 1;
    errno = 0;
    if (open("private", O_CREAT | O_WRONLY, 0666) != -1) return 2;
    if (errno != ENOSYS || open_calls != 0) return 3;
    errno = 0;
    if (mkdir("private-dir", 0777) != -1) return 4;
    if (errno != ENOSYS || mkdir_calls != 0) return 5;
    if (umask(022) != 077) return 6;
    return 0;
}
