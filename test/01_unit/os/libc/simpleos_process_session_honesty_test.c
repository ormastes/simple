#include <stdint.h>

int errno = 0;
static int64_t syscall_result = 1;
static int64_t seen_number = 0;
static int64_t seen_duration = 0;

int64_t simpleos_syscall(int64_t number, int64_t a, int64_t b, int64_t c, int64_t d, int64_t e) {
    (void)number; (void)a; (void)b; (void)c; (void)d; (void)e;
    seen_number = number;
    seen_duration = a;
    return syscall_result;
}

#define setsid simpleos_test_setsid
#define getsid simpleos_test_getsid
#define setpgid simpleos_test_setpgid
#define getuid simpleos_test_getuid
#define getgid simpleos_test_getgid
#define geteuid simpleos_test_geteuid
#define getegid simpleos_test_getegid
#define gethostname simpleos_test_gethostname
#define getpagesize simpleos_test_getpagesize
#define alarm simpleos_test_alarm
#define sleep simpleos_test_sleep
#define usleep simpleos_test_usleep
#define sysconf simpleos_test_sysconf
#define _exit simpleos_test_exit
#include "src/os/libc/simpleos_process.c"

int main(void) {
    errno = 0;
    if (simpleos_test_getuid() != (uid_t)-1 || errno != ENOSYS) return 1;
    errno = 0;
    if (simpleos_test_getgid() != (gid_t)-1 || errno != ENOSYS) return 2;
    errno = 0;
    if (simpleos_test_geteuid() != (uid_t)-1 || errno != ENOSYS) return 3;
    errno = 0;
    if (simpleos_test_getegid() != (gid_t)-1 || errno != ENOSYS) return 4;
    errno = 0;
    if (simpleos_test_setsid() != -1 || errno != ENOSYS) return 5;
    errno = 0;
    if (simpleos_test_getsid(1) != -1 || errno != ENOSYS) return 6;
    errno = 0;
    if (simpleos_test_setpgid(0, 0) != -1 || errno != ENOSYS) return 7;
    errno = 0;
    if (simpleos_test_alarm(5) != 5 || errno != ENOSYS) return 8;
    if (simpleos_test_alarm(0) != 0) return 9;
    syscall_result = -EINTR;
    errno = 0;
    if (simpleos_test_sleep(2) != 2 || errno != EINTR) return 10;
    errno = 0;
    if (simpleos_test_usleep(7) != -1 || errno != EINTR) return 11;
    syscall_result = 0;
    if (simpleos_test_sleep(2) != 0 || seen_number != 51 || seen_duration != 2000000000LL) return 12;
    if (simpleos_test_usleep(7) != 0 || seen_number != 51 || seen_duration != 7000LL) return 13;
    return 0;
}
