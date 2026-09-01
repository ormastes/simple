/*
 * SimpleOS Libc Shim — Signal handling
 *
 * Provides signal set operations and kernel delivery through kill/raise.
 * Kernel-owned disposition registration, user trampolines, and mask/pending
 * delivery are not available, so those APIs fail closed rather than retain
 * inert C-local state.
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
 * signal()/sigaction — unavailable without a kernel disposition owner
 * ==================================================================== */

typedef void (*sighandler_t)(int);

sighandler_t signal(int signum, sighandler_t handler) {
    if (signum < 1 || signum >= MAX_SIGNALS) { errno = EINVAL; return SIG_ERR; }
    if (signum == SIGKILL || signum == SIGSTOP) { errno = EINVAL; return SIG_ERR; }
    (void)handler;
    errno = ENOSYS;
    return SIG_ERR;
}

/* ====================================================================
 * sigaction() — POSIX signal action
 * ==================================================================== */

int sigaction(int signum, const struct sigaction *act,
              struct sigaction *oldact) {
    if (signum < 1 || signum >= MAX_SIGNALS) { errno = EINVAL; return -1; }
    if (signum == SIGKILL || signum == SIGSTOP) { errno = EINVAL; return -1; }
    /* The dispatch owner cannot install or report handler/default/ignore,
     * masked delivery, restart, alt-stack, or reset semantics. Reporting a
     * made-up default action is just as unsafe as accepting a new handler. */
    (void)act;
    (void)oldact;
    errno = ENOSYS;
    return -1;
}

/* ====================================================================
 * Signal set operations
 * ==================================================================== */

int sigemptyset(sigset_t *set) {
    if (!set) { errno = EFAULT; return -1; }
    set->__bits[0] = 0;
    return 0;
}

int sigfillset(sigset_t *set) {
    if (!set) { errno = EFAULT; return -1; }
    set->__bits[0] = ~0UL;
    return 0;
}

int sigaddset(sigset_t *set, int signum) {
    if (!set) { errno = EFAULT; return -1; }
    if (signum < 1 || signum >= MAX_SIGNALS) { errno = EINVAL; return -1; }
    set->__bits[0] |= (1UL << signum);
    return 0;
}

int sigdelset(sigset_t *set, int signum) {
    if (!set) { errno = EFAULT; return -1; }
    if (signum < 1 || signum >= MAX_SIGNALS) { errno = EINVAL; return -1; }
    set->__bits[0] &= ~(1UL << signum);
    return 0;
}

int sigismember(const sigset_t *set, int signum) {
    if (!set) { errno = EFAULT; return -1; }
    if (signum < 1 || signum >= MAX_SIGNALS) { errno = EINVAL; return -1; }
    return (set->__bits[0] >> signum) & 1;
}

/* ====================================================================
 * sigprocmask — query-only until the kernel owns masking and pending delivery
 * ==================================================================== */

int sigprocmask(int how, const sigset_t *set, sigset_t *oldset) {
    if (how != SIG_BLOCK && how != SIG_UNBLOCK && how != SIG_SETMASK) {
        errno = EINVAL;
        return -1;
    }
    (void)set;
    (void)oldset;
    errno = ENOSYS;
    return -1;
}

/*
 * sigpending — report signals that are blocked AND undelivered.
 *
 * This is not a stub. It is the correct result for SimpleOS's signal model:
 * sigprocmask() above is a documented no-op, so no signal is ever blocked,
 * so no signal can ever be left pending — every signal is delivered at once.
 * The pending set is therefore genuinely empty, and clearing the caller's set
 * reports that truthfully.
 *
 * Consumer: rt_signal_check() in src/runtime/simple_core/core_process.spl
 * calls sigpending() then sigismember(). It correctly observes "not pending".
 *
 * If SimpleOS ever gains real signal blocking, sigprocmask() must start
 * tracking a mask and this function must report (blocked & raised) from it.
 */
int sigpending(sigset_t *set) {
    if (!set) { errno = EFAULT; return -1; }
    return sigemptyset(set);
}

/* ====================================================================
 * kill / raise
 * ==================================================================== */

int kill(pid_t pid, int sig) {
    /* POSIX signal 0 is a liveness/permission probe and must never terminate
     * the task. GetTaskInfo accepts null output buffers, so the scheduler is
     * the sole liveness owner and no process-list command or /proc guess is
     * involved. */
    if (sig == 0) {
        int64_t probe = simpleos_syscall(6, (int64_t)pid, 0, 0, 0, 0);
        if (probe < 0) { errno = ESRCH; return -1; }
        return 0;
    }
    int64_t r = simpleos_syscall(7, (int64_t)pid, (int64_t)sig, 0, 0, 0);
    if (r < 0) { errno = (int)(-r); return -1; }
    return 0;
}

int raise(int sig) {
    return kill(getpid(), sig);
}
