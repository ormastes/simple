#ifndef SIMPLE_RUNTIME_SOSIX_FREEBSD_REAPER_V1_H
#define SIMPLE_RUNTIME_SOSIX_FREEBSD_REAPER_V1_H

/* Private building blocks for a dedicated, single-threaded supervisor.
 * Acquire before creating ANY children: FreeBSD does not retroactively adopt
 * existing children. A successful signal is not proof of retirement. Callers
 * must reap and check an empty status, and must prevent new forks at that point.
 * Reaper descendants are the kernel reaper tree, not a PID or process group.
 * Acquisition is once per supervisor; do not release or reacquire while any
 * owned descendants or receipts exist. Failure leaves output values untouched;
 * callers must check the return value. These helpers do not implement an owner,
 * token retirement, launch admission, or protection against nested reapers. */
#include <errno.h>
#include <stdint.h>
#include <stddef.h>
#if defined(__FreeBSD__)
#include <signal.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/procctl.h>
#endif

static int sosix_freebsd_reaper_acquire_v1(void) {
#if defined(__FreeBSD__)
    return procctl(P_PID, 0, PROC_REAP_ACQUIRE, NULL);
#else
    errno = ENOTSUP; return -1;
#endif
}

static int sosix_freebsd_reaper_kill_v1(uint32_t *signalled) {
    if (!signalled) { errno = EINVAL; return -1; }
#if defined(__FreeBSD__)
    struct procctl_reaper_status status;
    memset(&status, 0, sizeof(status));
    if (procctl(P_PID, 0, PROC_REAP_STATUS, &status) < 0) return -1;
    if (!(status.rs_flags & REAPER_STATUS_OWNED)) { errno = EPERM; return -1; }
    struct procctl_reaper_kill request;
    memset(&request, 0, sizeof(request));
    request.rk_sig = SIGKILL;
    if (procctl(P_PID, 0, PROC_REAP_KILL, &request) < 0) return -1;
    *signalled = request.rk_killed;
    return 0;
#else
    errno = ENOTSUP; return -1;
#endif
}

static int sosix_freebsd_reaper_status_v1(uint32_t *descendants) {
    if (!descendants) { errno = EINVAL; return -1; }
#if defined(__FreeBSD__)
    struct procctl_reaper_status status;
    memset(&status, 0, sizeof(status));
    if (procctl(P_PID, 0, PROC_REAP_STATUS, &status) < 0) return -1;
    if (!(status.rs_flags & REAPER_STATUS_OWNED)) { errno = EPERM; return -1; }
    *descendants = status.rs_descendants;
    return 0;
#else
    errno = ENOTSUP; return -1;
#endif
}
#endif
