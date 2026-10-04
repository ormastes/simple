/*
 * SimpleOS Socket Operations
 *
 * Implements socket/bind/listen/accept/connect/send/recv/sendto/recvfrom/
 * shutdown/setsockopt/getsockopt/getsockname/getpeername/socketpair on
 * top of the SimpleOS network syscalls, with a Linux-host raw-syscall
 * fallback so hosted dual-mode tests still work (same dual-mode pattern
 * as simpleos_fs.c).
 *
 * SimpleOS syscall numbers (from src/os/kernel/ipc/syscall.spl, dispatch
 * bodies now implemented in src/os/kernel/abi/syscall_shim_net.spl):
 *   70 = NetSocket   71 = NetBind      72 = NetListen
 *   73 = NetConnect  74 = NetAccept    75 = NetSendTo (connected-send only)
 *   76 = NetRecvFrom (connected-recv only)
 *   77 = NetIfConfig (still ENOSYS — no libc entry point uses it)
 *
 * NOT wired to any SimpleOS syscall (fail closed with ENOSYS, no kernel
 * dispatch id exists for these — see syscall_shim_net.spl's id ↔ op
 * table, which stops at 77):
 *   - shutdown(): no NetShutdown syscall id has been allocated.
 *   - explicit-destination sendto()/recvfrom() (UDP-style, unconnected):
 *     NetSendTo/NetRecvFrom only support the already-connected peer
 *     (posix_send()/posix_recv() in socket_compat.spl have no
 *     destination-address parameter); a non-NULL dest/src address
 *     returns EOPNOTSUPP instead of silently using the wrong peer.
 *   - getsockname()/getpeername()/socketpair(): no syscall ids exist.
 *
 * setsockopt()/getsockopt() have no kernel syscall path either; SO_REUSEADDR
 * is tracked entirely in libc (a real, non-fake per-fd flag) since the
 * SimpleOS backends do not yet enforce address-reuse semantics. All other
 * options return ENOPROTOOPT.
 */

#include "include/sys/socket.h"
#include "include/netinet/in.h"
#include "include/errno.h"
#include "include/string.h"

extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                 int64_t a2, int64_t a3, int64_t a4);
extern int errno;

static int running_on_linux_host(void) {
    return simpleos_syscall(4, 0, 0, 0, 0, 0) < 0;
}

/* ====================================================================
 * Linux-host raw syscall fallback (x86_64 only, matches simpleos_fs.c's
 * linux_syscall2/3 pattern extended to 6 args). Passing unused trailing
 * arguments as 0 to a syscall that takes fewer parameters is safe: the
 * kernel simply never reads those registers.
 * ==================================================================== */

#if defined(__x86_64__)
static int64_t linux_syscall6(int64_t id, int64_t a0, int64_t a1,
                               int64_t a2, int64_t a3, int64_t a4,
                               int64_t a5) {
    long ret;
    register long r10 __asm__("r10") = a3;
    register long r8  __asm__("r8")  = a4;
    register long r9  __asm__("r9")  = a5;
    __asm__ volatile("syscall"
                     : "=a"(ret)
                     : "a"(id), "D"(a0), "S"(a1), "d"(a2), "r"(r10),
                       "r"(r8), "r"(r9)
                     : "rcx", "r11", "memory");
    return ret;
}
#else
static int64_t linux_syscall6(int64_t id, int64_t a0, int64_t a1,
                               int64_t a2, int64_t a3, int64_t a4,
                               int64_t a5) {
    (void)id; (void)a0; (void)a1; (void)a2; (void)a3; (void)a4; (void)a5;
    return -ENOSYS;
}
#endif

/* Linux x86_64 socket syscall numbers */
#define LINUX_SYS_socket      41
#define LINUX_SYS_connect     42
#define LINUX_SYS_accept      43
#define LINUX_SYS_sendto      44
#define LINUX_SYS_recvfrom    45
#define LINUX_SYS_shutdown    48
#define LINUX_SYS_bind        49
#define LINUX_SYS_listen      50
#define LINUX_SYS_getsockname 51
#define LINUX_SYS_getpeername 52
#define LINUX_SYS_socketpair  53
#define LINUX_SYS_setsockopt  54
#define LINUX_SYS_getsockopt  55

/* ====================================================================
 * setsockopt(SO_REUSEADDR)/getsockopt(SO_REUSEADDR) — pure libc state.
 * No SimpleOS syscall exists for this; the SimpleOS netstack/loopback
 * backends do not enforce reuse semantics yet, so this only records the
 * caller's intent (a real value, not a fabricated one).
 * ==================================================================== */

#define SIMPLEOS_SOCKOPT_MAX_FD 256
static unsigned char g_so_reuseaddr[SIMPLEOS_SOCKOPT_MAX_FD];

static void sockopt_track_reuseaddr(int fd, int on) {
    if (fd >= 0 && fd < SIMPLEOS_SOCKOPT_MAX_FD)
        g_so_reuseaddr[fd] = on ? 1 : 0;
}

/* ====================================================================
 * socket() / bind() / listen() / connect() / accept()
 * ==================================================================== */

int socket(int domain, int type, int protocol) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_socket, domain, type, protocol,
                                    0, 0, 0);
        if (r < 0) { errno = (int)(-r); return -1; }
        return (int)r;
    }
    int64_t r = simpleos_syscall(70, domain, type, protocol, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return (int)r;
}

int bind(int sockfd, const struct sockaddr *addr, socklen_t addrlen) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_bind, sockfd, (int64_t)addr,
                                    addrlen, 0, 0, 0);
        if (r < 0) { errno = (int)(-r); return -1; }
        return 0;
    }
    int64_t r = simpleos_syscall(71, sockfd, (int64_t)addr, addrlen, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int listen(int sockfd, int backlog) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_listen, sockfd, backlog, 0,
                                    0, 0, 0);
        if (r < 0) { errno = (int)(-r); return -1; }
        return 0;
    }
    int64_t r = simpleos_syscall(72, sockfd, backlog, 0, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int connect(int sockfd, const struct sockaddr *addr, socklen_t addrlen) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_connect, sockfd, (int64_t)addr,
                                    addrlen, 0, 0, 0);
        if (r < 0) { errno = (int)(-r); return -1; }
        return 0;
    }
    int64_t r = simpleos_syscall(73, sockfd, (int64_t)addr, addrlen, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_accept, sockfd, (int64_t)addr,
                                    (int64_t)addrlen, 0, 0, 0);
        if (r < 0) { errno = (int)(-r); return -1; }
        return (int)r;
    }
    /* SimpleOS's NetAccept does not currently populate the peer address
     * (see syscall_shim_net.spl's spl_handle_net_accept) — if the caller
     * asked for it, the kernel zeroes *addrlen rather than leaving addr
     * untouched-but-claimed-valid. */
    int64_t r = simpleos_syscall(74, sockfd, (int64_t)addr, (int64_t)addrlen,
                                  0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return (int)r;
}

int shutdown(int sockfd, int how) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_shutdown, sockfd, how, 0,
                                    0, 0, 0);
        if (r < 0) { errno = (int)(-r); return -1; }
        return 0;
    }
    /* No SimpleOS syscall id has been allocated for shutdown() — see
     * this file's header comment. Fail closed rather than pretending a
     * half-close happened. */
    (void)sockfd; (void)how;
    errno = ENOSYS;
    return -1;
}

/* ====================================================================
 * send() / recv() / sendto() / recvfrom()
 * ==================================================================== */

long send(int sockfd, const void *buf, size_t len, int flags) {
    return sendto(sockfd, buf, len, flags, NULL, 0);
}

long recv(int sockfd, void *buf, size_t len, int flags) {
    return recvfrom(sockfd, buf, len, flags, NULL, NULL);
}

long sendto(int sockfd, const void *buf, size_t len, int flags,
            const struct sockaddr *dest_addr, socklen_t addrlen) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_sendto, sockfd, (int64_t)buf,
                                    (int64_t)len, flags, (int64_t)dest_addr,
                                    addrlen);
        if (r < 0) { errno = (int)(-r); return -1; }
        return (long)r;
    }
    if (dest_addr != NULL) {
        /* NetSendTo only sends to the socket's already-connected/
         * rendezvoused peer (see syscall_shim_net.spl); it cannot route
         * to an explicit destination. Reject rather than silently
         * sending to the wrong peer. */
        errno = EOPNOTSUPP;
        return -1;
    }
    int64_t r = simpleos_syscall(75, sockfd, (int64_t)buf, (int64_t)len,
                                  flags, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return (long)r;
}

long recvfrom(int sockfd, void *buf, size_t len, int flags,
              struct sockaddr *src_addr, socklen_t *addrlen) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_recvfrom, sockfd, (int64_t)buf,
                                    (int64_t)len, flags, (int64_t)src_addr,
                                    (int64_t)addrlen);
        if (r < 0) { errno = (int)(-r); return -1; }
        return (long)r;
    }
    if (src_addr != NULL) {
        /* NetRecvFrom cannot report the peer address (see
         * syscall_shim_net.spl); reject rather than returning data with
         * an unpopulated/fabricated source address. */
        errno = EOPNOTSUPP;
        return -1;
    }
    int64_t r = simpleos_syscall(76, sockfd, (int64_t)buf, (int64_t)len,
                                  flags, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return (long)r;
}

/* ====================================================================
 * setsockopt() / getsockopt()
 * ==================================================================== */

int setsockopt(int sockfd, int level, int optname, const void *optval,
               socklen_t optlen) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_setsockopt, sockfd, level,
                                    optname, (int64_t)optval, optlen, 0);
        if (r < 0) { errno = (int)(-r); return -1; }
        return 0;
    }
    if (level != SOL_SOCKET) { errno = ENOPROTOOPT; return -1; }
    if (optname == SO_REUSEADDR) {
        if (!optval || optlen < sizeof(int)) { errno = EINVAL; return -1; }
        int on;
        memcpy(&on, optval, sizeof(int));
        sockopt_track_reuseaddr(sockfd, on);
        return 0;
    }
    errno = ENOPROTOOPT;
    return -1;
}

int getsockopt(int sockfd, int level, int optname, void *optval,
               socklen_t *optlen) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_getsockopt, sockfd, level,
                                    optname, (int64_t)optval,
                                    (int64_t)optlen, 0);
        if (r < 0) { errno = (int)(-r); return -1; }
        return 0;
    }
    if (level != SOL_SOCKET) { errno = ENOPROTOOPT; return -1; }
    if (optname == SO_REUSEADDR) {
        if (!optval || !optlen || *optlen < sizeof(int)) {
            errno = EINVAL;
            return -1;
        }
        int on = (sockfd >= 0 && sockfd < SIMPLEOS_SOCKOPT_MAX_FD)
                     ? g_so_reuseaddr[sockfd]
                     : 0;
        memcpy(optval, &on, sizeof(int));
        *optlen = sizeof(int);
        return 0;
    }
    errno = ENOPROTOOPT;
    return -1;
}

/* ====================================================================
 * getsockname() / getpeername() / socketpair()
 *
 * No SimpleOS syscall ids exist for these; the Linux-host fallback
 * remains fully functional for hosted dual-mode tests.
 * ==================================================================== */

int getsockname(int sockfd, struct sockaddr *addr, socklen_t *addrlen) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_getsockname, sockfd,
                                    (int64_t)addr, (int64_t)addrlen, 0, 0, 0);
        if (r < 0) { errno = (int)(-r); return -1; }
        return 0;
    }
    (void)addr; (void)addrlen;
    errno = ENOSYS;
    return -1;
}

int getpeername(int sockfd, struct sockaddr *addr, socklen_t *addrlen) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_getpeername, sockfd,
                                    (int64_t)addr, (int64_t)addrlen, 0, 0, 0);
        if (r < 0) { errno = (int)(-r); return -1; }
        return 0;
    }
    (void)addr; (void)addrlen;
    errno = ENOSYS;
    return -1;
}

int socketpair(int domain, int type, int protocol, int sv[2]) {
    if (running_on_linux_host()) {
        int64_t r = linux_syscall6(LINUX_SYS_socketpair, domain, type,
                                    protocol, (int64_t)sv, 0, 0);
        if (r < 0) { errno = (int)(-r); return -1; }
        return 0;
    }
    /* No AF_UNIX / socketpair backend exists in the SimpleOS kernel
     * (posix_socket() rejects any domain != AF_INET). */
    (void)domain; (void)type; (void)protocol; (void)sv;
    errno = ENOSYS;
    return -1;
}
