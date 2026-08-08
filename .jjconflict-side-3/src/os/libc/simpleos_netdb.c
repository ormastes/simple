/*
 * simpleos_netdb.c — SimpleOS libc address conversion and resolution.
 *
 * inet_ntop / inet_pton are pure text<->binary conversions. They involve no
 * kernel and no name service, so they are implemented completely and exactly.
 *
 * getaddrinfo() is deliberately partial and says so at runtime: SimpleOS has
 * no DNS resolver, so it resolves numeric IPv4 literals and the AI_PASSIVE
 * wildcard for real and returns EAI_NONAME for names that would need a
 * nameserver. It never invents an address.
 */

#include "include/netdb.h"
#include "include/arpa/inet.h"
#include "include/netinet/in.h"
#include "include/sys/socket.h"
#include "include/string.h"
#include "include/stdlib.h"
#include "include/errno.h"

/* ====================================================================
 * inet_pton / inet_ntop (AF_INET only — SimpleOS has no IPv6 stack)
 * ==================================================================== */

int inet_pton(int af, const char *src, void *dst) {
    if (af != AF_INET) { errno = EAFNOSUPPORT; return -1; }
    if (!src || !dst) { errno = EFAULT; return -1; }

    uint32_t octets[4];
    int oi = 0;
    const char *p = src;

    for (oi = 0; oi < 4; oi++) {
        if (*p < '0' || *p > '9') return 0;     /* need >=1 digit */
        uint32_t v = 0;
        int digits = 0;
        while (*p >= '0' && *p <= '9') {
            v = v * 10u + (uint32_t)(*p - '0');
            if (++digits > 3 || v > 255u) return 0;
            p++;
        }
        /* Reject leading zeros ("01") — they read as octal to humans. */
        if (digits > 1 && src[0] == '0' && oi == 0 && p - src == digits && *src == '0')
            return 0;
        octets[oi] = v;
        if (oi < 3) {
            if (*p != '.') return 0;
            p++;
        }
    }
    if (*p != '\0') return 0;

    /* Network byte order: first octet is the most significant byte. */
    unsigned char *out = (unsigned char *)dst;
    out[0] = (unsigned char)octets[0];
    out[1] = (unsigned char)octets[1];
    out[2] = (unsigned char)octets[2];
    out[3] = (unsigned char)octets[3];
    return 1;
}

static char *_u8_to_dec(unsigned char v, char *out) {
    if (v >= 100) { *out++ = (char)('0' + v / 100); v %= 100; *out++ = (char)('0' + v / 10); }
    else if (v >= 10) { *out++ = (char)('0' + v / 10); }
    *out++ = (char)('0' + v % 10);
    return out;
}

const char *inet_ntop(int af, const void *src, char *dst, socklen_t size) {
    if (af != AF_INET) { errno = EAFNOSUPPORT; return NULL; }
    if (!src || !dst) { errno = EFAULT; return NULL; }

    char buf[INET_ADDRSTRLEN];
    const unsigned char *in = (const unsigned char *)src;
    char *w = buf;
    for (int i = 0; i < 4; i++) {
        w = _u8_to_dec(in[i], w);
        if (i < 3) *w++ = '.';
    }
    *w = '\0';

    size_t need = (size_t)(w - buf) + 1u;
    if ((size_t)size < need) { errno = ENOSPC; return NULL; }
    memcpy(dst, buf, need);
    return dst;
}

/* ====================================================================
 * getaddrinfo / freeaddrinfo
 * ==================================================================== */

const char *gai_strerror(int errcode) {
    switch (errcode) {
        case 0:            return "Success";
        case EAI_BADFLAGS: return "Invalid flags";
        case EAI_NONAME:   return "Name resolution requires DNS, which SimpleOS does not provide";
        case EAI_AGAIN:    return "Temporary failure in name resolution";
        case EAI_FAIL:     return "Non-recoverable failure in name resolution";
        case EAI_FAMILY:   return "Address family not supported";
        case EAI_SOCKTYPE: return "Socket type not supported";
        case EAI_SERVICE:  return "Service not supported for socket type";
        case EAI_MEMORY:   return "Memory allocation failure";
        case EAI_SYSTEM:   return "System error";
        case EAI_OVERFLOW: return "Argument buffer overflow";
        default:           return "Unknown error";
    }
}

/* Parse a decimal port. Returns -1 unless the whole string is 0..65535. */
static int _parse_port(const char *service) {
    if (!service || !*service) return 0;
    uint32_t v = 0;
    for (const char *p = service; *p; p++) {
        if (*p < '0' || *p > '9') return -1;
        v = v * 10u + (uint32_t)(*p - '0');
        if (v > 65535u) return -1;
    }
    return (int)v;
}

void freeaddrinfo(struct addrinfo *res) {
    while (res) {
        struct addrinfo *next = res->ai_next;
        /* ai_addr is allocated in the same block, right after the node. */
        free(res);
        res = next;
    }
}

int getaddrinfo(const char *node, const char *service,
                const struct addrinfo *hints, struct addrinfo **res) {
    if (!res) return EAI_SYSTEM;
    *res = NULL;

    int family   = hints ? hints->ai_family   : AF_UNSPEC;
    int socktype = hints ? hints->ai_socktype : 0;
    int protocol = hints ? hints->ai_protocol : 0;
    int flags    = hints ? hints->ai_flags    : 0;

    if (family != AF_UNSPEC && family != AF_INET) return EAI_FAMILY;

    int port = _parse_port(service);
    if (port < 0) {
        /* Named services need /etc/services, which SimpleOS does not have. */
        return EAI_SERVICE;
    }

    struct in_addr addr;
    if (!node) {
        /* No node: AI_PASSIVE means bind-any, otherwise loopback. */
        addr.s_addr = (flags & AI_PASSIVE) ? INADDR_ANY : INADDR_LOOPBACK;
    } else if (inet_pton(AF_INET, node, &addr) != 1) {
        /*
         * Not a numeric literal. Resolving it would require a DNS client,
         * which SimpleOS does not have. Fail truthfully rather than inventing
         * an address the caller would then connect to.
         */
        return EAI_NONAME;
    }

    /* One allocation holds the node and its sockaddr_in. */
    size_t need = sizeof(struct addrinfo) + sizeof(struct sockaddr_in);
    struct addrinfo *ai = (struct addrinfo *)malloc(need);
    if (!ai) return EAI_MEMORY;
    memset(ai, 0, need);

    struct sockaddr_in *sin = (struct sockaddr_in *)((char *)ai + sizeof(struct addrinfo));
    sin->sin_family = AF_INET;
    sin->sin_port   = htons((uint16_t)port);
    sin->sin_addr   = addr;

    ai->ai_family   = AF_INET;
    ai->ai_socktype = socktype ? socktype : SOCK_STREAM;
    ai->ai_protocol = protocol;
    ai->ai_addrlen  = (socklen_t)sizeof(struct sockaddr_in);
    ai->ai_addr     = (struct sockaddr *)sin;
    ai->ai_flags    = flags;
    ai->ai_canonname = NULL;
    ai->ai_next     = NULL;

    *res = ai;
    return 0;
}
