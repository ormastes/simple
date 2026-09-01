#include <stdint.h>
#include "src/os/libc/include/poll.h"

int errno;

int poll(struct pollfd *fds, unsigned long nfds, int timeout) {
    (void)fds;
    (void)nfds;
    (void)timeout;
    return 0;
}

#include "src/os/libc/simpleos_epoll.c"

int main(void) {
    struct epoll_event events[1];
    unsigned long mask = 0;
    int epfd = epoll_create1(0);
    if (epfd < 0) return 1;
    errno = 0;
    if (epoll_pwait(epfd, events, 1, 0, &mask) != -1 || errno != ENOSYS) return 2;
    if (epoll_pwait(epfd, events, 1, 0, NULL) != 0) return 3;
    return 0;
}
