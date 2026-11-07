#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
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

#include "runtime_local_unix_v1.h"

/* Public native leaves remain in .c for the exact owner census. The included
 * implementation shares the one local-connection registry and reader. */
SplArray* rt_local_unix_connect_v1(const char* p,int64_t n,int64_t u,int64_t d) {
    return lu_connect_impl_v1(p,n,u,d);
}
SplArray* rt_local_unix_read_v1(int64_t t,int64_t m,int64_t d) {
    return lu_read_impl_v1(t,m,d);
}
SplArray* rt_local_unix_write_some_v1(int64_t t,SplArray* b,int64_t o,int64_t m,int64_t d) {
    return lu_write_v1(t,b,o,m,d,0,0);
}
SplArray* rt_local_unix_write_some_admitted_v1(int64_t t,SplArray* b,int64_t o,int64_t m,int64_t d,int64_t e) {
    return lu_write_v1(t,b,o,m,d,1,e);
}
SplArray* rt_local_unix_close_v1(int64_t t) {
    return lu_close_impl_v1(t);
}
