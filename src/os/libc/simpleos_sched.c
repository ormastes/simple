#include "include/sched.h"
#include "include/errno.h"
#include <stdint.h>

/* Kernel ABI: process/scheduler yield.  This is intentionally not a host
 * syscall fallback: syscall number 1 has an unrelated meaning on Linux. */
#define SIMPLEOS_SYS_YIELD 1

extern int64_t simpleos_syscall(int64_t, int64_t, int64_t, int64_t,
                                 int64_t, int64_t);
extern int errno;

int sched_yield(void) {
    int64_t result = simpleos_syscall(SIMPLEOS_SYS_YIELD, 0, 0, 0, 0, 0);
    if (result < 0) {
        errno = (int)(-result);
        return -1;
    }
    return 0;
}
