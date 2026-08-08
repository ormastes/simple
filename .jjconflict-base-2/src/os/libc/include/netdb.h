/*
 * netdb.h — SimpleOS libc name/service resolution.
 *
 * SimpleOS has no DNS resolver. getaddrinfo() therefore resolves what it can
 * resolve WITHOUT a nameserver — numeric IPv4 literals, the AI_PASSIVE
 * wildcard, and numeric ports — for real, and returns EAI_NONAME for anything
 * that would need a DNS lookup.
 *
 * That is a truthful failure, not a fabricated success: a caller asking to
 * resolve "example.com" gets a resolution error it can report, never a bogus
 * address it would then silently connect to.
 */
#ifndef _NETDB_H
#define _NETDB_H

#include <stddef.h>
#include <sys/socket.h>
#include <netinet/in.h>

#ifdef __cplusplus
extern "C" {
#endif

struct addrinfo {
    int              ai_flags;
    int              ai_family;
    int              ai_socktype;
    int              ai_protocol;
    socklen_t        ai_addrlen;
    struct sockaddr *ai_addr;
    char            *ai_canonname;
    struct addrinfo *ai_next;
};

/* ai_flags */
#define AI_PASSIVE      0x0001
#define AI_CANONNAME    0x0002
#define AI_NUMERICHOST  0x0004
#define AI_V4MAPPED     0x0008
#define AI_ALL          0x0010
#define AI_ADDRCONFIG   0x0020
#define AI_NUMERICSERV  0x0400

/* getaddrinfo error codes (glibc-compatible values) */
#define EAI_BADFLAGS    -1
#define EAI_NONAME      -2
#define EAI_AGAIN       -3
#define EAI_FAIL        -4
#define EAI_FAMILY      -6
#define EAI_SOCKTYPE    -7
#define EAI_SERVICE     -8
#define EAI_MEMORY      -10
#define EAI_SYSTEM      -11
#define EAI_OVERFLOW    -12

int  getaddrinfo(const char *node, const char *service,
                 const struct addrinfo *hints, struct addrinfo **res);
void freeaddrinfo(struct addrinfo *res);
const char *gai_strerror(int errcode);

#ifdef __cplusplus
}
#endif

#endif /* _NETDB_H */
