#include <errno.h>
#ifndef ENOSYS
#define ENOSYS 38
#endif
int eventfd(unsigned int initval, int flags) {
    (void)initval; (void)flags; errno = ENOSYS; return -1;
}
int eventfd_read(int fd, unsigned long long *value) {
    (void)fd; (void)value; errno = ENOSYS; return -1;
}
int eventfd_write(int fd, unsigned long long value) {
    (void)fd; (void)value; errno = ENOSYS; return -1;
}
