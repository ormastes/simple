#include <stdint.h>

int errno = 0;
static int64_t syscall_result = 0;
static int64_t syscall_number = 0;
int64_t simpleos_syscall(int64_t number, int64_t a, int64_t b, int64_t c, int64_t d, int64_t e) {
    (void)a; (void)b; (void)c; (void)d; (void)e;
    syscall_number = number;
    return syscall_result;
}

#define getppid simpleos_test_getppid
#define getuid simpleos_test_getuid
#define getgid simpleos_test_getgid
#define geteuid simpleos_test_geteuid
#define getegid simpleos_test_getegid
#define setsid simpleos_test_setsid
#define getsid simpleos_test_getsid
#define setpgid simpleos_test_setpgid
#define gethostname simpleos_test_gethostname
#define getpagesize simpleos_test_getpagesize
#define alarm simpleos_test_alarm
#define sleep simpleos_test_sleep
#define usleep simpleos_test_usleep
#define sysconf simpleos_test_sysconf
#define _exit simpleos_test_exit
#include "src/os/libc/simpleos_process.c"

int main(void) {
    syscall_result = 42;
    errno = 0;
    if (simpleos_test_getppid() != 42 || syscall_number != 9 || errno != 0) return 1;
    syscall_result = -4;
    errno = 0;
    if (simpleos_test_getppid() != (pid_t)-1 || syscall_number != 9 || errno != 4) return 2;
    size_t allocated = 0;
    if (_env_entry_size((size_t)-1, 0, &allocated)) return 3;
    if (_env_entry_size((size_t)-2, 0, &allocated)) return 4;
    errno = 0;
    if (getenv(0) != 0 || errno != EINVAL) return 5;
    errno = 0;
    if (setenv(0, "x", 1) != -1 || errno != EINVAL) return 6;
    errno = 0;
    if (setenv("", "x", 1) != -1 || errno != EINVAL) return 7;
    errno = 0;
    if (setenv("A=B", "x", 1) != -1 || errno != EINVAL) return 8;
    errno = 0;
    if (setenv("A", 0, 1) != -1 || errno != EINVAL) return 9;
    if (setenv("SAFE", "first", 1) != 0) return 7;
    if (!getenv("SAFE") || strcmp(getenv("SAFE"), "first") != 0) return 8;
    if (setenv("SAFE", "second", 1) != 0) return 9;
    if (!getenv("SAFE") || strcmp(getenv("SAFE"), "second") != 0) return 10;
    if (setenv("SAFE", "ignored", 0) != 0 || strcmp(getenv("SAFE"), "second") != 0) return 11;
    if (unsetenv("SAFE") != 0 || getenv("SAFE") != 0 || environ[0] != 0) return 12;
    errno = 0;
    if (unsetenv("A=B") != -1 || errno != EINVAL) return 13;
    return 0;
}
