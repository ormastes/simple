/*
 * SimpleOS pipe/dup2/dup — IF-01 syscall trampoline.
 * Fallback to -ENOSYS when SIMPLEOS_HAS_SYSCALL_TRAMPOLINE undefined.
 */

#include <errno.h>
#include <stdint.h>

#ifdef SIMPLEOS_HAS_SYSCALL_TRAMPOLINE
extern long _simpleos_syscall1(long num, long a);
extern long _simpleos_syscall2(long num, long a, long b);
#else
static inline long _simpleos_syscall1(long n, long a) { (void)n;(void)a; return -38; }
static inline long _simpleos_syscall2(long n, long a, long b) { (void)n;(void)a;(void)b; return -38; }
#endif

#define SYS_PIPE 53
#define SYS_DUP2 54
#define SYS_DUP  55

int simpleos_pipe(int pipefd[2]) {
    long ret = _simpleos_syscall1(SYS_PIPE, (long)(uintptr_t)pipefd);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    return 0;
}

int pipe2(int pipefd[2], int flags) {
    (void)flags;
    return simpleos_pipe(pipefd);
}

int simpleos_dup2(int oldfd, int newfd) {
    long ret = _simpleos_syscall2(SYS_DUP2, (long)oldfd, (long)newfd);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    return (int)ret;
}

int simpleos_dup(int oldfd) {
    long ret = _simpleos_syscall1(SYS_DUP, (long)oldfd);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    return (int)ret;
}

int dup3(int oldfd, int newfd, int flags) {
    (void)flags;
    return simpleos_dup2(oldfd, newfd);
}

int socketpair(int domain, int type, int protocol, int sv[2]) {
    (void)domain; (void)type; (void)protocol; (void)sv;
    errno = 38;
    return -1;
}
