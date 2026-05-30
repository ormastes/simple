/*
 * SimpleOS Libc Shim — Signal handling
 *
 * Provides signal handler registration and dispatch, signal set operations,
 * and kill/raise. Single-threaded; sigprocmask is a no-op.
 *
 * Signal numbers match src/os/posix/signal_compat.spl and <signal.h>.
 * Syscall 7 = Kill(pid, sig).
 */

#include "include/signal.h"
#include "include/errno.h"
#include "include/string.h"
#include "include/unistd.h"

extern int64_t simpleos_syscall(int64_t, int64_t, int64_t, int64_t,
                                 int64_t, int64_t);
extern int errno;

#define MAX_SIGNALS 32

/* ====================================================================
 * Signal action table
 * ==================================================================== */

static struct sigaction _sig_actions[MAX_SIGNALS];
static int _sig_initialized = 0;

static void _init_signals(void) {
    if (_sig_initialized) return;
    for (int i = 0; i < MAX_SIGNALS; i++) {
        _sig_actions[i].sa_handler = SIG_DFL;
        sigemptyset(&_sig_actions[i].sa_mask);
        _sig_actions[i].sa_flags = 0;
    }
    _sig_initialized = 1;
}

/* ====================================================================
 * signal() — simple handler registration (returns old handler)
 * ==================================================================== */

typedef void (*sighandler_t)(int);

sighandler_t signal(int signum, sighandler_t handler) {
    if (signum < 1 || signum >= MAX_SIGNALS) { errno = EINVAL; return SIG_ERR; }
    if (signum == SIGKILL || signum == SIGSTOP) { errno = EINVAL; return SIG_ERR; }
    _init_signals();
    sighandler_t old = _sig_actions[signum].sa_handler;
    _sig_actions[signum].sa_handler = handler;
    return old;
}

/* ====================================================================
 * sigaction() — POSIX signal action
 * ==================================================================== */

int sigaction(int signum, const struct sigaction *act,
              struct sigaction *oldact) {
    if (signum < 1 || signum >= MAX_SIGNALS) { errno = EINVAL; return -1; }
    if (signum == SIGKILL || signum == SIGSTOP) { errno = EINVAL; return -1; }
    _init_signals();
    if (oldact) *oldact = _sig_actions[signum];
    if (act)    _sig_actions[signum] = *act;
    return 0;
}

/* ====================================================================
 * Signal set operations
 * ==================================================================== */

int sigemptyset(sigset_t *set) {
    set->__bits[0] = 0;
    return 0;
}

int sigfillset(sigset_t *set) {
    set->__bits[0] = ~0UL;
    return 0;
}

int sigaddset(sigset_t *set, int signum) {
    if (signum < 1 || signum >= MAX_SIGNALS) { errno = EINVAL; return -1; }
    set->__bits[0] |= (1UL << signum);
    return 0;
}

int sigdelset(sigset_t *set, int signum) {
    if (signum < 1 || signum >= MAX_SIGNALS) { errno = EINVAL; return -1; }
    set->__bits[0] &= ~(1UL << signum);
    return 0;
}

int sigismember(const sigset_t *set, int signum) {
    if (signum < 1 || signum >= MAX_SIGNALS) { errno = EINVAL; return -1; }
    return (set->__bits[0] >> signum) & 1;
}

/* ====================================================================
 * sigprocmask — no-op (single-threaded)
 * ==================================================================== */

int sigprocmask(int how, const sigset_t *set, sigset_t *oldset) {
    (void)how; (void)set; (void)oldset;
    return 0;
}

/* ====================================================================
 * kill / raise
 * ==================================================================== */

int kill(pid_t pid, int sig) {
    int64_t r = simpleos_syscall(7, (int64_t)pid, (int64_t)sig, 0, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int raise(int sig) {
    return kill(getpid(), sig);
}
