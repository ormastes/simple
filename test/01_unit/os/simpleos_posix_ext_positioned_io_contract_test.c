#include <assert.h>
#include <stddef.h>

static int seek_calls;
static int read_calls;
static int write_calls;

#define pread simpleos_test_pread
#define pwrite simpleos_test_pwrite
#define lseek simpleos_test_lseek
#define read simpleos_test_read
#define write simpleos_test_write
#include "../../../src/os/libc/simpleos_posix_ext.c"
#undef write
#undef read
#undef lseek
#undef pwrite
#undef pread

int errno;

off_t simpleos_test_lseek(int fd, off_t offset, int whence)
{
    (void)fd;
    (void)offset;
    (void)whence;
    seek_calls++;
    return 0;
}

ssize_t simpleos_test_read(int fd, void *buf, size_t count)
{
    (void)fd;
    (void)buf;
    (void)count;
    read_calls++;
    return 0;
}

ssize_t simpleos_test_write(int fd, const void *buf, size_t count)
{
    (void)fd;
    (void)buf;
    (void)count;
    write_calls++;
    return 0;
}

int main(void)
{
    unsigned char byte = 0;

    errno = 0;
    assert(simpleos_test_pread(7, &byte, 1, 4) == -1);
    assert(errno == ENOTSUP);

    errno = 0;
    assert(simpleos_test_pwrite(7, &byte, 1, 4) == -1);
    assert(errno == ENOTSUP);

    assert(seek_calls == 0);
    assert(read_calls == 0);
    assert(write_calls == 0);

    errno = 123;
    assert(simpleos_test_pread(7, &byte, 0, 4) == 0);
    assert(errno == 123);

    errno = 124;
    assert(simpleos_test_pwrite(7, &byte, 0, 4) == 0);
    assert(errno == 124);

    assert(seek_calls == 0);
    assert(read_calls == 0);
    assert(write_calls == 0);
    return 0;
}
