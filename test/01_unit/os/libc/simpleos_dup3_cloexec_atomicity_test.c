/* Regression: guest dup3(O_CLOEXEC) must fail before replacing newfd. */

#include <stdint.h>

int errno = 0;
static int dup2_syscall_calls = 0;

int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4)
{
    (void)a0;
    (void)a1;
    (void)a2;
    (void)a3;
    (void)a4;
    if (id == 63) dup2_syscall_calls++;
    return 0;
}

void simpleos_epoll_on_fd_close(int fd) { (void)fd; }
void simpleos_epoll_on_fd_close_token(int fd, uint64_t token)
{
    (void)fd;
    (void)token;
}

#define dup3 simpleos_test_dup3
#undef __x86_64__
#include "src/os/libc/simpleos_ipc.c"

int main(void)
{
    errno = 0;
    if (simpleos_test_dup3(3, 4, O_CLOEXEC) != -1) return 1;
    if (errno != ENOSYS) return 2;
    if (dup2_syscall_calls != 0) return 3;
    return 0;
}
