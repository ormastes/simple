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

typedef unsigned int socklen_t;

struct sockaddr {
    unsigned short sa_family;
    char sa_data[14];
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

#ifdef __cplusplus
}
#endif

#endif
