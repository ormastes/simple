/* Minimal hosted syscall/layout shim for Pure-Simple nonblocking policy.
 * prepare: -1 failure, -2 completed Windows ioctl, or POSIX status flags.
 */
#include <stdbool.h>
#include <stdint.h>

#if !defined(_WIN32)
#include <fcntl.h>
int64_t rt_socket_nonblock_prepare(int64_t fd, int64_t mode) {
    (void)mode;
    return (int64_t)fcntl((int)fd, F_GETFL, 0);
}
int64_t rt_socket_nonblock_commit(int64_t fd, int64_t flags) {
    return (int64_t)fcntl((int)fd, F_SETFL, (int)flags);
}
int64_t rt_socket_nonblock_mask(void) { return (int64_t)O_NONBLOCK; }
#else
#include <winsock2.h>
int64_t rt_socket_nonblock_prepare(int64_t fd, int64_t requested_mode) {
    u_long mode = (u_long)requested_mode;
    return ioctlsocket((SOCKET)fd, FIONBIO, &mode) == 0 ? -2 : -1;
}
int64_t rt_socket_nonblock_commit(int64_t fd, int64_t flags) {
    (void)fd; (void)flags; return -1;
}
int64_t rt_socket_nonblock_mask(void) { return 0; }
#endif
