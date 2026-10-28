#include "../runtime_sosix_freebsd_image_v1.h"
#include <assert.h>
#if defined(__FreeBSD__)
#include <string.h>
#endif
int main(void) {
    const uint8_t bytes[] = {1, 2, 3, 4};
    assert(sosix_freebsd_stage_image_v1(NULL, 0) < 0 && errno == EINVAL);
#if defined(__FreeBSD__)
    int fd = sosix_freebsd_stage_image_v1(bytes, sizeof(bytes));
    assert(fd >= 0);
    struct stat st;
    assert(fstat(fd, &st) == 0 && S_ISREG(st.st_mode) && st.st_nlink == 0);
    assert((fcntl(fd, F_GETFL) & O_ACCMODE) == O_RDONLY);
    assert((fcntl(fd, F_GETFD) & FD_CLOEXEC) != 0);
    uint8_t actual[sizeof(bytes)];
    assert(pread(fd, actual, sizeof(actual), 0) == (ssize_t)sizeof(actual));
    assert(memcmp(actual, bytes, sizeof(bytes)) == 0);
    assert(write(fd, bytes, sizeof(bytes)) < 0);
    int copy = fcntl(fd, F_DUPFD_CLOEXEC, 3);
    assert(copy >= 0 && close(fd) == 0);
    assert(pread(copy, actual, sizeof(actual), 0) == (ssize_t)sizeof(actual));
    assert(close(copy) == 0);
#else
    assert(sosix_freebsd_stage_image_v1(bytes, sizeof(bytes)) < 0 && errno == ENOTSUP);
#endif
    return 0;
}
