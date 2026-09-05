#include <errno.h>
#include <stdint.h>

/* The freestanding libc ABI owns a global errno, unlike host libc TLS. */
int errno = 0;

int64_t simpleos_syscall(int64_t number, int64_t a, int64_t b, int64_t c, int64_t d, int64_t e) {
    (void)number; (void)a; (void)b; (void)c; (void)d; (void)e;
    return 0;
}

#define signal simpleos_test_signal
#define sigaction simpleos_test_sigaction
#define sigprocmask simpleos_test_sigprocmask
#define sigpending simpleos_test_sigpending
#define kill simpleos_test_kill
#define raise simpleos_test_raise
#define strsignal simpleos_test_strsignal
#include "src/os/libc/simpleos_signal.c"

int main(void) {
    sigset_t set;
    sigset_t oldset;
    struct sigaction action;
    sigemptyset(&set);
    sigaddset(&set, SIGTERM);
    oldset.__bits[0] = 0xfeedUL;
    errno = 0;
    if (simpleos_test_sigprocmask(SIG_BLOCK, &set, &oldset) != -1 || errno != ENOSYS) return 1;
    if (oldset.__bits[0] != 0xfeedUL) return 2;
    errno = 0;
    if (simpleos_test_sigprocmask(99, 0, 0) != -1 || errno != EINVAL) return 3;
    oldset.__bits[0] = 0xfeedUL;
    errno = 0;
    if (simpleos_test_sigprocmask(SIG_SETMASK, 0, &oldset) != -1 || errno != ENOSYS || oldset.__bits[0] != 0xfeedUL) return 4;
    action.sa_handler = SIG_DFL;
    action.sa_mask = set;
    action.sa_flags = 0;
    errno = 0;
    if (simpleos_test_sigaction(SIGTERM, &action, 0) != -1 || errno != ENOSYS) return 5;
    action.sa_mask.__bits[0] = 0;
    action.sa_flags = SA_RESTART;
    errno = 0;
    if (simpleos_test_sigaction(SIGTERM, &action, 0) != -1 || errno != ENOSYS) return 6;
    errno = 0;
    if (simpleos_test_signal(SIGTERM, SIG_DFL) != SIG_ERR || errno != ENOSYS) return 7;
    action.sa_handler = SIG_IGN;
    action.sa_mask.__bits[0] = 0xfeedUL;
    action.sa_flags = SA_RESTART;
    errno = 0;
    if (simpleos_test_sigaction(SIGTERM, 0, &action) != -1 || errno != ENOSYS || action.sa_handler != SIG_IGN || action.sa_mask.__bits[0] != 0xfeedUL || action.sa_flags != SA_RESTART) return 8;
    errno = 0;
    if (sigemptyset(0) != -1 || errno != EFAULT) return 9;
    errno = 0;
    if (sigfillset(0) != -1 || errno != EFAULT) return 10;
    errno = 0;
    if (sigaddset(0, SIGTERM) != -1 || errno != EFAULT) return 11;
    errno = 0;
    if (sigdelset(0, SIGTERM) != -1 || errno != EFAULT) return 12;
    errno = 0;
    if (sigismember(0, SIGTERM) != -1 || errno != EFAULT) return 13;
    return 0;
}
