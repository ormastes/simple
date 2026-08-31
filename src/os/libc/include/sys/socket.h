#ifndef SIMPLEOS_SYS_SOCKET_H
#define SIMPLEOS_SYS_SOCKET_H

#include <stddef.h>
#include <sys/types.h>

#define AF_UNIX 1
#define AF_LOCAL AF_UNIX
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
#define SO_BROADCAST  6

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

/* AF_INET / AF_INET6 and sa_family_t were MISSING from this header while
 * <netinet/in.h> included it and used `sa_family_t` for sockaddr_in::sin_family
 * and sockaddr_in6::sin6_family, and src/runtime/runtime_native.c used AF_INET
 * directly. The result was
 *   netinet/in.h:44:5: error: unknown type name 'sa_family_t'
 *   runtime_native.c:5537:23: error: use of undeclared identifier 'AF_INET'
 * so the Simple runtime could never be cross-compiled for SimpleOS.
 *
 * The VALUES are not invented: AF_UNIX is already 1 here (the Linux number), and
 * the kernel's own shim pins AF_INET — `val _AF_INET: u16 = 2` at
 * src/os/kernel/abi/syscall_shim_net.spl:17, with the comment at :73 spelling
 * out "AF_INET=2, AF_INET6=10". These match Linux, which is what the rest of the
 * header already assumed. sa_family_t is `unsigned short` so that
 * sockaddr_in::sin_family lands at offset 0 with size 2, exactly what
 * spl_handle_net_bind/connect read, and so struct sockaddr's own `unsigned short
 * sa_family` below stays layout-identical. */
#define AF_INET  2
#define AF_INET6 10

typedef unsigned short sa_family_t;
typedef unsigned int socklen_t;

struct sockaddr {
    unsigned short sa_family;
    char sa_data[14];
};

/* struct sockaddr_storage was missing while src/runtime/runtime_native.c:12245
 * declares one ("variable has incomplete type"). It is the POSIX
 * "big enough for any address family, correctly aligned" type; 128 bytes and
 * 8-byte alignment are the standard Linux/BSD choices, and 128 comfortably holds
 * this libc's largest family (sockaddr_in6, 28 bytes). */
struct sockaddr_storage {
    sa_family_t ss_family;
    char        __ss_padding[126];
    /* Force 8-byte alignment without depending on <stdalign.h>. */
    long long   __ss_align_dummy[0];
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
/* The send/recv family was likewise absent while runtime_native.c calls it,
 * producing "call to undeclared function 'sendto'" and friends. Signatures are
 * the POSIX ones; simpleos_socket.c provides the definitions. */
long send(int sockfd, const void *buf, unsigned long len, int flags);
long recv(int sockfd, void *buf, unsigned long len, int flags);
long sendto(int sockfd, const void *buf, unsigned long len, int flags,
            const struct sockaddr *dest_addr, socklen_t addrlen);
long recvfrom(int sockfd, void *buf, unsigned long len, int flags,
              struct sockaddr *src_addr, socklen_t *addrlen);
int getsockopt(int sockfd, int level, int optname, void *optval,
               socklen_t *optlen);
int getsockname(int sockfd, struct sockaddr *addr, socklen_t *addrlen);
int getpeername(int sockfd, struct sockaddr *addr, socklen_t *addrlen);

#ifdef __cplusplus
}
#endif

#endif
