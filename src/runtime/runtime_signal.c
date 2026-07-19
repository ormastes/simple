/* Hosted signal and process-exit polling shared by Rust-hosted and core-C runtimes. */

#include <stdint.h>
#include <signal.h>
#include <stdlib.h>

static volatile sig_atomic_t signal_flags[32] = {0};
static volatile sig_atomic_t process_exit_flag = 0;

static void simple_signal_handler(int signal_num) {
    if (signal_num >= 0 && signal_num < 32) {
        signal_flags[signal_num] = 1;
    }
}

static void simple_process_exit_handler(void) {
    process_exit_flag = 1;
}

int64_t rt_signal_install(int64_t signal_num) {
    if (signal_num < 0 || signal_num >= 32) return 0;
#ifdef _WIN32
    return signal((int)signal_num, simple_signal_handler) == SIG_ERR ? 0 : 1;
#else
    struct sigaction action;
    action.sa_handler = simple_signal_handler;
    sigemptyset(&action.sa_mask);
    action.sa_flags = SA_RESTART;
    return sigaction((int)signal_num, &action, NULL) == -1 ? 0 : 1;
#endif
}

int64_t rt_signal_check(int64_t signal_num) {
    if (signal_num < 0 || signal_num >= 32) return 0;
    if (!signal_flags[signal_num]) return 0;
    signal_flags[signal_num] = 0;
    return 1;
}

int64_t rt_atexit_install(void) {
    static int installed = 0;
    if (!installed) {
        if (atexit(simple_process_exit_handler) != 0) return 0;
        installed = 1;
    }
    return 1;
}

int64_t rt_atexit_check(void) {
    if (!process_exit_flag) return 0;
    process_exit_flag = 0;
    return 1;
}
