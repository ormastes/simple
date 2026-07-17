#include <stdint.h>
#include <signal.h>
#include <stdlib.h>

/*
 * Signal/atexit latches for the Rust-hosted runtime bundle.
 *
 * The exact core-C bundle owns the same ABI in runtime.c.  Keep this provider
 * separate so hosted binaries do not need to link the monolithic core runtime
 * (which would duplicate the Rust value ABI).
 */
static volatile sig_atomic_t hosted_signal_flags[32] = {0};
static volatile sig_atomic_t hosted_atexit_flag = 0;

static void hosted_signal_handler(int signum) {
    if (signum >= 0 && signum < 32) hosted_signal_flags[signum] = 1;
}

static void hosted_atexit_handler(void) {
    hosted_atexit_flag = 1;
}

int64_t rt_signal_install(int64_t signal_num) {
    if (signal_num < 0 || signal_num >= 32) return 0;
#ifdef _WIN32
    /* Windows has no sigaction; C-standard signal() covers the latch use case. */
    return signal((int)signal_num, hosted_signal_handler) != SIG_ERR ? 1 : 0;
#else
    struct sigaction action;
    action.sa_handler = hosted_signal_handler;
    sigemptyset(&action.sa_mask);
    action.sa_flags = SA_RESTART;
    return sigaction((int)signal_num, &action, NULL) == 0 ? 1 : 0;
#endif
}

int64_t rt_signal_check(int64_t signal_num) {
    if (signal_num < 0 || signal_num >= 32) return 0;
    if (!hosted_signal_flags[signal_num]) return 0;
    hosted_signal_flags[signal_num] = 0;
    return 1;
}

int64_t rt_atexit_install(void) {
    static int installed = 0;
    if (!installed) {
        if (atexit(hosted_atexit_handler) != 0) return 0;
        installed = 1;
    }
    return 1;
}

int64_t rt_atexit_check(void) {
    if (!hosted_atexit_flag) return 0;
    hosted_atexit_flag = 0;
    return 1;
}
