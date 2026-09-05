#include <stdint.h>

int errno = 0;
static int close_calls[2];
static int close_count = 0;
static int fcntl_calls = 0;

int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4) {
    (void)a1; (void)a2; (void)a3; (void)a4;
    if (id == 62) {
        int *pair = (int *)(uintptr_t)a0;
        pair[0] = 41;
        pair[1] = 42;
        return 0;
    }
    return -38;
}

void simpleos_epoll_on_fd_close(int fd) { (void)fd; }
void simpleos_epoll_on_fd_close_token(int fd, uint64_t token) { (void)fd; (void)token; }

int simpleos_test_fcntl(int fd, int command, ...) {
    (void)fd;
    (void)command;
    fcntl_calls++;
    errno = 5;
    return -1;
}

int simpleos_test_close(int fd) {
    if (close_count < 2) close_calls[close_count] = fd;
    close_count++;
    return 0;
}

#define fcntl simpleos_test_fcntl
#define close simpleos_test_close
#define pipe simpleos_test_pipe
#define pipe2 simpleos_test_pipe2
#define dup2 simpleos_test_dup2
#define dup simpleos_test_dup
#define dup3 simpleos_test_dup3
#undef __x86_64__
#include "src/os/libc/simpleos_ipc.c"

int main(void) {
    int pair[2] = { -1, -1 };
    errno = 0;
    if (simpleos_test_pipe(NULL) != -1 || errno != EFAULT) return 1;
    errno = 0;
    if (simpleos_test_pipe2(NULL, 0) != -1 || errno != EFAULT) return 2;
    errno = 0;
    if (simpleos_test_pipe2(pair, O_CLOEXEC) != -1 || errno != 5) return 3;
    if (fcntl_calls != 1 || close_count != 2) return 4;
    if (close_calls[0] != 41 || close_calls[1] != 42) return 5;
    return 0;
}
