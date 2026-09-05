/* Regression: ppoll must not claim an atomic signal-mask transition. */

#include <stdint.h>

int errno = 0;
static int syscall_calls = 0;

int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4)
{
    (void)id;
    (void)a0;
    (void)a1;
    (void)a2;
    (void)a3;
    (void)a4;
    syscall_calls++;
    return 0;
}

#include "src/os/libc/simpleos_poll.c"

int main(void)
{
    struct pollfd fd = { .fd = 3, .events = POLLIN, .revents = 0 };
    unsigned long mask = 0;

    errno = 0;
    if (ppoll(&fd, 1, NULL, &mask) != -1) return 1;
    if (errno != ENOSYS) return 2;
    if (syscall_calls != 0) return 3;
    if (ppoll(&fd, 1, NULL, NULL) != 0) return 4;
    if (syscall_calls != 1) return 5;
    return 0;
}
