/*
 * SimpleOS poll wrappers.
 */

#include <errno.h>
#include <stdint.h>
#include <time.h>
#include <poll.h>

extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                int64_t a2, int64_t a3, int64_t a4);

#define SYS_POLL 68

int poll(struct pollfd *fds, nfds_t nfds, int timeout) {
    if (!fds && nfds != 0) {
        errno = EFAULT;
        return -1;
    }
    int64_t ret = simpleos_syscall(SYS_POLL, (int64_t)(uintptr_t)fds,
                                   (int64_t)nfds, (int64_t)timeout, 0, 0);
    if (ret < 0) {
        errno = (int)(-ret);
        return -1;
    }
    return (int)ret;
}

int ppoll(struct pollfd *fds, nfds_t nfds, const struct timespec *tmo_p, const void *sigmask) {
    (void)sigmask;
    int timeout = -1;
    if (tmo_p) {
        if (tmo_p->tv_sec < 0 || tmo_p->tv_nsec < 0 || tmo_p->tv_nsec >= 1000000000L) {
            errno = EINVAL;
            return -1;
        }
        int64_t ms = (int64_t)tmo_p->tv_sec * 1000 + (int64_t)((tmo_p->tv_nsec + 999999L) / 1000000L);
        timeout = ms > 2147483647LL ? 2147483647 : (int)ms;
    }
    return poll(fds, nfds, timeout);
}
