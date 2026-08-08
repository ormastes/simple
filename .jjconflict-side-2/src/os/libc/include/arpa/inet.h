/*
 * arpa/inet.h — SimpleOS libc address presentation/conversion.
 *
 * inet_ntop/inet_pton are pure text<->binary conversions with no kernel
 * involvement, so they are fully implemented (simpleos_netdb.c).
 */
#ifndef _ARPA_INET_H
#define _ARPA_INET_H

#include <stdint.h>
#include <sys/socket.h>
#include <netinet/in.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifndef INET_ADDRSTRLEN
#define INET_ADDRSTRLEN  16
#endif
#ifndef INET6_ADDRSTRLEN
#define INET6_ADDRSTRLEN 46
#endif

const char *inet_ntop(int af, const void *src, char *dst, socklen_t size);
int         inet_pton(int af, const char *src, void *dst);

#ifdef __cplusplus
}
#endif

#endif /* _ARPA_INET_H */
