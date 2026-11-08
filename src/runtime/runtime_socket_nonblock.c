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
    return lu_read_impl_v1(t,m,d,0,0);
}
SplArray* rt_local_unix_write_some_v1(int64_t t,SplArray* b,int64_t o,int64_t m,int64_t d) {
    return lu_write_v1(t,b,o,m,d,0,0,0);
}
SplArray* rt_local_unix_write_some_admitted_v1(int64_t t,SplArray* b,int64_t o,int64_t m,int64_t d,int64_t e) {
    return lu_write_v1(t,b,o,m,d,1,e,0);
}
SplArray* rt_local_unix_close_v1(int64_t t) {
    return lu_close_impl_v1(t);
}

SplArray* rt_local_unix_listen_v1(const char* p,int64_t n,int64_t u,int64_t b) {
    return lu_listen_impl_v1(p,n,u,b);
}
SplArray* rt_local_unix_accept_v1(int64_t t,int64_t u) { return lu_accept_impl_v1(t,u); }
SplArray* rt_local_unix_poll_v1(int64_t t,int64_t r,int64_t w) { return lu_poll_impl_v1(t,r,w); }
SplArray* rt_local_unix_read_now_v1(int64_t t,int64_t m) { return lu_read_impl_v1(t,m,0,1,0); }
SplArray* rt_local_unix_write_some_now_v1(int64_t t,SplArray* b,int64_t o,int64_t m) {
    return lu_write_v1(t,b,o,m,0,0,0,1);
}
SplArray* rt_local_unix_listener_close_v1(int64_t t) { return lu_listener_close_impl_v1(t); }

SplArray* rt_local_unix_peer_v1(int64_t t) { return lu_peer_impl_v1(t); }

SplArray* rt_local_unix_shutdown_write_v1(int64_t t) { return lu_shutdown_write_impl_v1(t); }

SplArray* rt_local_unix_claim_request_v1(int64_t t,const char* r,int64_t n) { return lu_claim_request_impl_v1(t,r,n); }

/* Private cross-owner origin check; no descriptor or allocator is exposed. */
int simple_local_unix_origin_v1(void) {
#if defined(__linux__)
    return lu_origin_v1();
#else
    return 0;
#endif
}

SplArray* rt_local_unix_stage_stdout_v1(int64_t t,int64_t p,int64_t g,const char* r,int64_t rn,
        const char* i,int64_t in,const char* b,int64_t bn) {
    return lu_stage_stdout_impl_v1(t,p,g,r,rn,i,in,b,bn);
}
SplArray* rt_local_unix_read_handoff_now_v1(int64_t t,int64_t m) { return lu_read_impl_v1(t,m,0,1,1); }
SplArray* rt_local_unix_adopt_byte_endpoint_v1(int64_t t,const char* b,int64_t n) { return lu_adopt_byte_impl_v1(t,b,n); }
SplArray* rt_local_unix_handoff_state_v1(int64_t t) { return lu_handoff_state_impl_v1(t); }
