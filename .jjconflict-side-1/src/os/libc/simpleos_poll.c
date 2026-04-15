/*
 * SimpleOS poll stubs — poll, ppoll
 *
 * SimpleOS has no async I/O. All fds return POLLNVAL so callers fail loudly
 * instead of deadlocking on a never-ready descriptor.
 */

#include <errno.h>

typedef unsigned long nfds_t;

struct pollfd {
    int fd;
    short events;
    short revents;
};

struct timespec;

#ifndef POLLNVAL
#define POLLNVAL 0x0020
#endif

int poll(struct pollfd *fds, nfds_t nfds, int timeout) {
    (void)timeout;
    if (!fds) {
        errno = EFAULT;
        return -1;
    }
    for (nfds_t i = 0; i < nfds; i++) {
        fds[i].revents = POLLNVAL;
    }
    return (int)nfds;
}

int ppoll(struct pollfd *fds, nfds_t nfds, const struct timespec *tmo_p, const void *sigmask) {
    (void)tmo_p; (void)sigmask;
    return poll(fds, nfds, 0);
}
