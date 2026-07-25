/*
 * SimpleOS <poll.h>
 */

#ifndef _SIMPLEOS_POLL_H
#define _SIMPLEOS_POLL_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>

typedef unsigned long nfds_t;

struct pollfd {
    int   fd;
    short events;
    short revents;
};

#define POLLIN      0x0001
#define POLLPRI     0x0002
#define POLLOUT     0x0004
#define POLLERR     0x0008
#define POLLHUP     0x0010
#define POLLNVAL    0x0020

struct timespec;

int poll(struct pollfd *fds, nfds_t nfds, int timeout);
int ppoll(struct pollfd *fds, nfds_t nfds, const struct timespec *tmo_p, const void *sigmask);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_POLL_H */
