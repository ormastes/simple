#ifndef SIMPLEOS_SYS_SOCKET_H
#define SIMPLEOS_SYS_SOCKET_H

#include <stddef.h>
#include <sys/types.h>

/* Address families.
 * AF_INET/AF_INET6 numeric values match the domain check in the kernel
 * network syscall handlers (src/os/kernel/ipc/syscall_net.spl
 * _handle_net_socket: "arg0 != 2" rejects anything but AF_INET; the
 * comment there documents AF_INET6=10). AF_UNIX is a SimpleOS-local
 * value (no kernel unix-domain backend exists yet). */
#define AF_UNSPEC   0
#define AF_UNIX     1
#define AF_LOCAL    AF_UNIX
#define AF_INET     2
#define AF_INET6    10
#define PF_UNSPEC   AF_UNSPEC
#define PF_UNIX     AF_UNIX
#define PF_INET     AF_INET
#define PF_INET6    AF_INET6

/* Socket types. Numeric values match the kernel's proto mapping in
 * _handle_net_socket (type==1 -> TCP proto 1, type==2 -> UDP proto 2). */
#define SOCK_STREAM 1
#define SOCK_DGRAM  2
#define SOCK_RAW    3

/* setsockopt/getsockopt levels and options. Only SO_REUSEADDR is
 * accepted by the SimpleOS backend today; every other optname returns
 * ENOPROTOOPT (see simpleos_socket.c). */
#define SOL_SOCKET    1
#define SO_REUSEADDR  2
#define SO_KEEPALIVE  9
#define SO_ERROR      4
#define SO_RCVTIMEO   20
#define SO_SNDTIMEO   21

/* shutdown() how values (POSIX/BSD numbering). */
#define SHUT_RD   0
#define SHUT_WR   1
#define SHUT_RDWR 2

/* send()/recv() flags. SimpleOS's netstack/loopback backends do not
 * implement any of these yet; they are accepted (non-fatal) but
 * currently have no effect. */
#define MSG_OOB       0x01
#define MSG_PEEK      0x02
#define MSG_DONTROUTE 0x04
#define MSG_WAITALL   0x100
#define MSG_NOSIGNAL  0x4000
#define MSG_DONTWAIT  0x40

typedef unsigned int socklen_t;
typedef unsigned short sa_family_t;

struct sockaddr {
    sa_family_t sa_family;
    char sa_data[14];
};

/* Generic storage large enough for sockaddr_in / sockaddr_in6 (matches
 * the BSD/llvm-libc convention referenced for conformance). */
struct sockaddr_storage {
    sa_family_t ss_family;
    char ss_padding[126];
};

#ifdef __cplusplus
extern "C" {
#endif

int socket(int domain, int type, int protocol);
int connect(int sockfd, const struct sockaddr *addr, socklen_t addrlen);
int bind(int sockfd, const struct sockaddr *addr, socklen_t addrlen);
int listen(int sockfd, int backlog);
int accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen);
int shutdown(int sockfd, int how);
int setsockopt(int sockfd, int level, int optname, const void *optval,
               socklen_t optlen);
int getsockopt(int sockfd, int level, int optname, void *optval,
               socklen_t *optlen);

long send(int sockfd, const void *buf, size_t len, int flags);
long recv(int sockfd, void *buf, size_t len, int flags);
long sendto(int sockfd, const void *buf, size_t len, int flags,
            const struct sockaddr *dest_addr, socklen_t addrlen);
long recvfrom(int sockfd, void *buf, size_t len, int flags,
              struct sockaddr *src_addr, socklen_t *addrlen);

int getsockname(int sockfd, struct sockaddr *addr, socklen_t *addrlen);
int getpeername(int sockfd, struct sockaddr *addr, socklen_t *addrlen);
int socketpair(int domain, int type, int protocol, int sv[2]);

#ifdef __cplusplus
}
#endif

#endif
