#include <errno.h>
#ifndef ENOSYS
#define ENOSYS 38
#endif
struct itimerspec;
int timerfd_create(int clockid, int flags) {
    (void)clockid; (void)flags; errno = ENOSYS; return -1;
}
int timerfd_settime(int fd, int flags, const struct itimerspec *new_value, struct itimerspec *old_value) {
    (void)fd; (void)flags; (void)new_value; (void)old_value; errno = ENOSYS; return -1;
}
int timerfd_gettime(int fd, struct itimerspec *curr_value) {
    (void)fd; (void)curr_value; errno = ENOSYS; return -1;
}
