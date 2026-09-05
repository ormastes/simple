/*
 * Regression: fread/fwrite must reject an element-count multiplication that
 * cannot be represented as a byte count, before issuing any I/O syscall.
 */

#include <stdint.h>
#include "src/os/libc/include/errno.h"

typedef unsigned int useconds_t;

int errno = 0;
static int read_calls = 0;
static int write_calls = 0;

int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4)
{
    (void)id;
    (void)a0;
    (void)a1;
    (void)a2;
    (void)a3;
    (void)a4;
    return -ENOSYS;
}

#include "src/os/libc/simpleos_fs.c"

ssize_t read(int fd, void *buf, size_t count)
{
    (void)fd;
    (void)buf;
    (void)count;
    read_calls++;
    return 1;
}

ssize_t write(int fd, const void *buf, size_t count)
{
    (void)fd;
    (void)buf;
    (void)count;
    write_calls++;
    return 1;
}

int main(void)
{
    struct __simpleos_FILE stream = { .fd = 7, .eof = 0, .error = 0, .mode = 0 };
    unsigned char byte = 0;

    errno = 0;
    if (fread(&byte, (size_t)-1, 2, &stream) != 0) return 1;
    if (errno != EOVERFLOW || stream.error == 0 || read_calls != 0) return 2;

    stream.error = 0;
    errno = 0;
    if (fwrite(&byte, (size_t)-1, 2, &stream) != 0) return 3;
    if (errno != EOVERFLOW || stream.error == 0 || write_calls != 0) return 4;
    return 0;
}
