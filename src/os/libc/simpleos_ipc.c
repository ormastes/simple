/*
 * SimpleOS pipe/dup2/dup — IF-01 syscall wrappers.
 */

#include <errno.h>
#include <stdint.h>
#include <fcntl.h>

extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                int64_t a2, int64_t a3, int64_t a4);
extern void simpleos_epoll_on_fd_close(int fd);
extern void simpleos_epoll_on_fd_close_token(int fd, uint64_t ofd_token);

#define SYS_PIPE 62
#define SYS_DUP2 63
#define SYS_DUP  64

static int simpleos_valid_fd_flags(int flags) {
    return (flags & ~(O_CLOEXEC | O_NONBLOCK)) == 0;
}

int pipe(int pipefd[2]) {
    long ret = (long)simpleos_syscall(SYS_PIPE,
                                      (long)(uintptr_t)pipefd, 0, 0, 0, 0);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    return 0;
}

int pipe2(int pipefd[2], int flags) {
    if (!simpleos_valid_fd_flags(flags)) {
        errno = EINVAL;
        return -1;
    }
    if (pipe(pipefd) < 0) return -1;

    if (flags & O_CLOEXEC) {
        if (fcntl(pipefd[0], F_SETFD, FD_CLOEXEC) < 0 ||
            fcntl(pipefd[1], F_SETFD, FD_CLOEXEC) < 0) {
            return -1;
        }
    }
    if (flags & O_NONBLOCK) {
        int rflags = fcntl(pipefd[0], F_GETFL, 0);
        int wflags = fcntl(pipefd[1], F_GETFL, 0);
        if (rflags < 0 || wflags < 0) return -1;
        if (fcntl(pipefd[0], F_SETFL, rflags | O_NONBLOCK) < 0 ||
            fcntl(pipefd[1], F_SETFL, wflags | O_NONBLOCK) < 0) {
            return -1;
        }
    }
    return 0;
}

int dup2(int oldfd, int newfd) {
    int replaced_ofd = -1;
    if (oldfd != newfd) {
        int saved_errno = errno;
        replaced_ofd = fcntl(newfd, F_SIMPLEOS_GET_OFD, 0);
        errno = saved_errno;
    }
    long ret = (long)simpleos_syscall(SYS_DUP2,
                                      (long)oldfd, (long)newfd, 0, 0, 0);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    if (oldfd != newfd && replaced_ofd >= 0) {
        simpleos_epoll_on_fd_close_token(newfd, (uint64_t)(uint32_t)replaced_ofd);
    }
    return (int)ret;
}

int dup(int oldfd) {
    long ret = (long)simpleos_syscall(SYS_DUP, (long)oldfd, 0, 0, 0, 0);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    return (int)ret;
}

int dup3(int oldfd, int newfd, int flags) {
    if (oldfd == newfd || (flags & ~O_CLOEXEC) != 0) {
        errno = EINVAL;
        return -1;
    }
    int fd = dup2(oldfd, newfd);
    if (fd < 0) return -1;
    if (flags & O_CLOEXEC) {
        if (fcntl(fd, F_SETFD, FD_CLOEXEC) < 0) return -1;
    }
    return fd;
}

int socketpair(int domain, int type, int protocol, int sv[2]) {
    (void)domain; (void)type; (void)protocol; (void)sv;
    errno = ENOSYS;
    return -1;
}
