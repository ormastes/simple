/*
 * SimpleOS pipe/dup2/dup — IF-01 syscall wrappers.
 */

#include <errno.h>
#include <stdint.h>

extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                int64_t a2, int64_t a3, int64_t a4);

#define SYS_PIPE 62
#define SYS_DUP2 63
#define SYS_DUP  64

int pipe(int pipefd[2]) {
    long ret = (long)simpleos_syscall(SYS_PIPE,
                                      (long)(uintptr_t)pipefd, 0, 0, 0, 0);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    return 0;
}

int pipe2(int pipefd[2], int flags) {
    (void)flags;
    return pipe(pipefd);
}

int dup2(int oldfd, int newfd) {
    long ret = (long)simpleos_syscall(SYS_DUP2,
                                      (long)oldfd, (long)newfd, 0, 0, 0);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    return (int)ret;
}

int dup(int oldfd) {
    long ret = (long)simpleos_syscall(SYS_DUP, (long)oldfd, 0, 0, 0, 0);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    return (int)ret;
}

int dup3(int oldfd, int newfd, int flags) {
    (void)flags;
    return dup2(oldfd, newfd);
}

int socketpair(int domain, int type, int protocol, int sv[2]) {
    (void)domain; (void)type; (void)protocol; (void)sv;
    errno = ENOSYS;
    return -1;
}
