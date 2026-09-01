/*
 * SimpleOS <netinet/in.h> — IPv4/IPv6 socket address definitions
 *
 * struct sockaddr_in layout (16 bytes: family(2) + port(2) + addr(4) +
 * zero-pad(8)) follows the standard BSD/llvm-libc conformance layout so
 * that on-wire bytes written by this header are byte-for-byte what
 * simpleos_socket.c parses via the kernel net syscalls (see
 * src/os/kernel/abi/syscall_shim_net.spl spl_handle_net_bind/connect,
 * which read family/port/addr at fixed offsets 0/2/4 from the user
 * pointer). Do not reorder or resize these fields without updating both
 * sides.
 *
 * sin_port and sin_addr.s_addr are in network byte order, matching
 * POSIX. htons()/ntohs()/htonl()/ntohl() below assume a little-endian
 * host (x86_64/aarch64/riscv — the only SimpleOS targets).
 */

#ifndef _SIMPLEOS_NETINET_IN_H
#define _SIMPLEOS_NETINET_IN_H

#include <stdint.h>
#include <sys/socket.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef uint16_t in_port_t;
typedef uint32_t in_addr_t;

struct in_addr {
    in_addr_t s_addr;   /* network byte order */
};

/* struct in6_addr — present for header completeness; SimpleOS has no
 * IPv6 backend yet (kernel domain check only special-cases AF_INET
 * numerically; AF_INET6 is accepted at the socket() layer per the
 * syscall_net.spl comment but has no bind/connect/send/recv path). */
struct in6_addr {
    unsigned char s6_addr[16];
};

struct sockaddr_in {
    sa_family_t    sin_family;   /* AF_INET */
    in_port_t      sin_port;     /* network byte order */
    struct in_addr sin_addr;     /* network byte order */
    unsigned char  sin_zero[8];  /* padding to sizeof(struct sockaddr) */
};

struct sockaddr_in6 {
    sa_family_t     sin6_family;   /* AF_INET6 */
    in_port_t       sin6_port;     /* network byte order */
    uint32_t        sin6_flowinfo;
    struct in6_addr sin6_addr;
    uint32_t        sin6_scope_id;
};

/* Well-known addresses (network byte order == host byte order for
 * these symmetric values). */
#define INADDR_ANY       ((in_addr_t)0x00000000u)
#define INADDR_BROADCAST ((in_addr_t)0xFFFFFFFFu)
#define INADDR_LOOPBACK  ((in_addr_t)0x0100007Fu) /* 127.0.0.1, wire order */

#define IPPROTO_IP   0
#define IPPROTO_ICMP 1
#define IPPROTO_TCP  6
#define IPPROTO_UDP  17
#define IPPROTO_IPV6 41

/* Multicast socket options and their argument structs were missing while
 * src/runtime/runtime_native.c:12250-12275 uses all of them — "use of undeclared
 * identifier 'IP_MULTICAST_LOOP'", "variable has incomplete type 'struct
 * ip_mreq'", and so on — blocking the SimpleOS runtime cross-compile.
 *
 * Values are the Linux ones, consistent with every other number in this header
 * and with the kernel shim's AF_INET=2. SimpleOS has no multicast backend, so
 * setsockopt with these will report unsupported; declaring them makes the tree
 * compile and lets that refusal be explicit rather than an implicit-declaration
 * guess. Do NOT read these as a claim that multicast works. */
#define IP_MULTICAST_IF     32
#define IP_MULTICAST_TTL    33
#define IP_MULTICAST_LOOP   34
#define IP_ADD_MEMBERSHIP   35
#define IP_DROP_MEMBERSHIP  36

#define IPV6_MULTICAST_IF   17
#define IPV6_MULTICAST_HOPS 18
#define IPV6_MULTICAST_LOOP 19
#define IPV6_JOIN_GROUP     20
#define IPV6_LEAVE_GROUP    21
#define IPV6_ADD_MEMBERSHIP  IPV6_JOIN_GROUP
#define IPV6_DROP_MEMBERSHIP IPV6_LEAVE_GROUP

struct ip_mreq {
    struct in_addr imr_multiaddr;   /* IP multicast address of group */
    struct in_addr imr_interface;   /* local IP address of interface */
};

struct ipv6_mreq {
    struct in6_addr ipv6mr_multiaddr;  /* IPv6 multicast address */
    unsigned int    ipv6mr_interface;  /* interface index */
};

static inline uint16_t htons(uint16_t hostshort) {
    return (uint16_t)((hostshort << 8) | (hostshort >> 8));
}

static inline uint16_t ntohs(uint16_t netshort) {
    return htons(netshort);
}

static inline uint32_t htonl(uint32_t hostlong) {
    return ((hostlong & 0x000000FFu) << 24) |
           ((hostlong & 0x0000FF00u) << 8)  |
           ((hostlong & 0x00FF0000u) >> 8)  |
           ((hostlong & 0xFF000000u) >> 24);
}

static inline uint32_t ntohl(uint32_t netlong) {
    return htonl(netlong);
}

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_NETINET_IN_H */
