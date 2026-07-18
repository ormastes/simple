#include "include/sys/statvfs.h"
#include "include/errno.h"

int statvfs(const char *path, struct statvfs *buf) {
    (void)path;
    (void)buf;
    errno = ENOSYS;
    return -1;
}

int fstatvfs(int fd, struct statvfs *buf) {
    (void)fd;
    (void)buf;
    errno = ENOSYS;
    return -1;
}
