/*
 * netinet/tcp.h — SimpleOS libc TCP-level socket options.
 *
 * Values match Linux so wire-compatible code and the SimpleOS network stack
 * agree. Only optnames the stack actually honours are accepted by
 * setsockopt(); the rest return ENOPROTOOPT (see simpleos_socket.c).
 */
#ifndef _NETINET_TCP_H
#define _NETINET_TCP_H

#define TCP_NODELAY   1
#define TCP_MAXSEG    2
#define TCP_KEEPIDLE  4
#define TCP_KEEPINTVL 5
#define TCP_KEEPCNT   6

#endif /* _NETINET_TCP_H */
