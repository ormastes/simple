#include "include/sys/socket.h"
#include "include/errno.h"

static int socket_enosys(void) {
    errno = ENOSYS;
    return -1;
}

int socket(int domain, int type, int protocol) {
    (void)domain; (void)type; (void)protocol;
    return socket_enosys();
}

int connect(int sockfd, const struct sockaddr *addr, socklen_t addrlen) {
    (void)sockfd; (void)addr; (void)addrlen;
    return socket_enosys();
}

int bind(int sockfd, const struct sockaddr *addr, socklen_t addrlen) {
    (void)sockfd; (void)addr; (void)addrlen;
    return socket_enosys();
}

int listen(int sockfd, int backlog) {
    (void)sockfd; (void)backlog;
    return socket_enosys();
}

int accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen) {
    (void)sockfd; (void)addr; (void)addrlen;
    return socket_enosys();
}

int shutdown(int sockfd, int how) {
    (void)sockfd; (void)how;
    return socket_enosys();
}

int setsockopt(int sockfd, int level, int optname, const void *optval,
               socklen_t optlen) {
    (void)sockfd; (void)level; (void)optname; (void)optval; (void)optlen;
    return socket_enosys();
}
