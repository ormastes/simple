#ifndef SIMPLEOS_SYS_SOCKET_H
#define SIMPLEOS_SYS_SOCKET_H

#include <stddef.h>
#include <sys/types.h>

#define AF_UNIX 1
#define AF_LOCAL AF_UNIX
#define SOCK_STREAM 1
#define SOL_SOCKET 1
#define SO_REUSEADDR 2

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
