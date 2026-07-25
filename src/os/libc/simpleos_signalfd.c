#include <errno.h>
#ifndef ENOSYS
#define ENOSYS 38
#endif
int signalfd(int fd, const void *mask, int flags) {
    (void)fd; (void)mask; (void)flags; errno = ENOSYS; return -1;
}
