#include <errno.h>
#include <sys/resource.h>
#include <sys/types.h>

static int waitpid_calls = 0;

pid_t simpleos_waitpid(pid_t pid, int *wstatus, int options) {
    (void)wstatus;
    (void)options;
    waitpid_calls++;
    return pid;
}

#define waitpid simpleos_test_waitpid
#define wait simpleos_test_wait
#define wait4 simpleos_test_wait4
#define popen simpleos_test_popen
#define pclose simpleos_test_pclose
#define system simpleos_test_system
#define getrusage simpleos_test_getrusage
#define getrlimit simpleos_test_getrlimit
#define setrlimit simpleos_test_setrlimit
#include "src/os/libc/simpleos_process_wait.c"

int main(void) {
    struct rusage usage;
    struct rlimit limit = { 1, 1 };

    errno = 0;
    if (simpleos_test_wait4(77, 0, 0, &usage) != (pid_t)-1 || errno != ENOSYS || waitpid_calls != 0) return 1;
    if (simpleos_test_wait4(77, 0, 0, 0) != 77 || waitpid_calls != 1) return 2;
    errno = 0;
    if (simpleos_test_getrusage(0, &usage) != -1 || errno != ENOSYS) return 3;
    errno = 0;
    if (simpleos_test_getrlimit(RLIMIT_DATA, &limit) != -1 || errno != ENOSYS) return 4;
    errno = 0;
    if (simpleos_test_setrlimit(RLIMIT_DATA, &limit) != -1 || errno != ENOSYS) return 5;
    errno = 0;
    if (simpleos_test_setrlimit(-1, &limit) != -1 || errno != EINVAL) return 6;
    return 0;
}
