#include <stdint.h>
#include <errno.h>

int errno = 0;
static int64_t syscall_result = 0;
static int64_t seen_number = 0;
static int64_t seen_nanos = 0;

int64_t simpleos_syscall(int64_t number, int64_t a, int64_t b, int64_t c, int64_t d, int64_t e) {
    (void)b; (void)c; (void)d; (void)e;
    seen_number = number;
    seen_nanos = a;
    return syscall_result;
}

#define clock_gettime simpleos_test_clock_gettime
#define gettimeofday simpleos_test_gettimeofday
#define time simpleos_test_time
#define clock simpleos_test_clock
#define nanosleep simpleos_test_nanosleep
#include "src/os/libc/simpleos_time.c"

int main(void) {
    struct timespec req = { 2, 3 };
    struct timespec rem = { 7, 8 };
    errno = 0;
    if (simpleos_test_nanosleep(0, &rem) != -1 || errno != EFAULT || rem.tv_sec != 7) return 1;
    req.tv_nsec = 1000000000L;
    errno = 0;
    if (simpleos_test_nanosleep(&req, &rem) != -1 || errno != EINVAL) return 2;
    req.tv_nsec = 3;
    syscall_result = -EINTR;
    errno = 0;
    if (simpleos_test_nanosleep(&req, &rem) != -1 || errno != EINTR || rem.tv_sec != 7) return 3;
    syscall_result = 0;
    if (simpleos_test_nanosleep(&req, &rem) != 0 || seen_number != 51 || seen_nanos != 2000000003LL || rem.tv_sec != 0 || rem.tv_nsec != 0) return 4;
    errno = 0;
    if (simpleos_test_clock_gettime(CLOCK_REALTIME, 0) != -1 || errno != EFAULT) return 5;
    errno = 0;
    if (simpleos_test_gettimeofday(0, 0) != -1 || errno != EFAULT) return 6;
    return 0;
}
