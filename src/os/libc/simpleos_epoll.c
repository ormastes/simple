/* SimpleOS: no async I/O — epoll fails-loud. */
#include <errno.h>

#ifndef ENOSYS
#define ENOSYS 38
#endif

int epoll_create(int size) { (void)size; errno = ENOSYS; return -1; }
int epoll_create1(int flags) { (void)flags; errno = ENOSYS; return -1; }
int epoll_ctl(int epfd, int op, int fd, void *event) {
    (void)epfd; (void)op; (void)fd; (void)event;
    errno = ENOSYS; return -1;
}
int epoll_wait(int epfd, void *events, int maxevents, int timeout) {
    (void)epfd; (void)events; (void)maxevents; (void)timeout;
    errno = ENOSYS; return -1;
}
int epoll_pwait(int epfd, void *events, int maxevents, int timeout, const void *sigmask) {
    (void)epfd; (void)events; (void)maxevents; (void)timeout; (void)sigmask;
    errno = ENOSYS; return -1;
}
