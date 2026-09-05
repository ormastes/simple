#include <stdint.h>

int errno = 0;
static int64_t syscall_result = 0;
static int64_t syscall_id = -1;
static int64_t syscall_args[5];

int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4) {
    syscall_id = id;
    syscall_args[0] = a0;
    syscall_args[1] = a1;
    syscall_args[2] = a2;
    syscall_args[3] = a3;
    syscall_args[4] = a4;
    return syscall_result;
}

#define sched_yield simpleos_test_sched_yield
#include "src/os/libc/simpleos_sched.c"

int main(void) {
    syscall_result = 0;
    errno = 0;
    if (simpleos_test_sched_yield() != 0) return 1;
    if (syscall_id != 1) return 2;
    for (int i = 0; i < 5; ++i) if (syscall_args[i] != 0) return 3;

    syscall_result = -4; /* EINTR in the guest errno ABI. */
    errno = 0;
    if (simpleos_test_sched_yield() != -1 || errno != 4) return 4;
    return 0;
}
