/* Darwin kernel coalition retirement primitives.
 * Caller must establish authority for the coalition through a trusted broker.
 * These functions do NOT establish launch admission, credential confinement,
 * or zombie reaping, and do NOT advertise process V4 capability.
 */
#ifndef RUNTIME_SOSIX_DARWIN_COALITION_PRIVATE_H
#define RUNTIME_SOSIX_DARWIN_COALITION_PRIVATE_H
#ifdef __APPLE__
#include <libproc.h>
#include <dlfcn.h>
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#ifndef SOSIX_DARWIN_COALITION_AFTER_CENSUS
#define SOSIX_DARWIN_COALITION_AFTER_CENSUS() ((void)0)
#endif

typedef struct { uint64_t ids[2], reserved[3]; } SosixDarwinCoalitionInfo;
typedef struct {
    unsigned char uuid[16];
    uint64_t unique_id, parent_unique_id;
    int32_t pid_version, original_parent_version;
    uint64_t reserved[2];
} SosixDarwinProcessIdentity;
_Static_assert(sizeof(SosixDarwinProcessIdentity) == 56, "Darwin identity ABI");
_Static_assert(sizeof(SosixDarwinCoalitionInfo) == 40, "Darwin coalition ABI");

typedef struct {
    uint64_t started, exited;
    unsigned passes, signal_count;
    int tasks_empty;
    /* Empty task accounting is explicitly not a zombie-reap receipt. */
    int all_reaped;
} SosixDarwinCoalitionRetirement;

static int sosix_darwin_coalition_info(pid_t pid, SosixDarwinCoalitionInfo *out) {
    int n = proc_pidinfo(pid, 20 /* PROC_PIDCOALITIONINFO */, 0, out, sizeof(*out));
    return n == sizeof(*out) ? 0 : (n == 0 && errno ? errno : EPROTO);
}

static int sosix_darwin_coalition_identity(pid_t pid, SosixDarwinProcessIdentity *out,
        int include_zombies) {
    int n = proc_pidinfo(pid, 17 /* PROC_PIDUNIQIDENTIFIERINFO */,
        include_zombies != 0, out, sizeof(*out));
    return n == sizeof(*out) ? 0 : (n == 0 && errno ? errno : EPROTO);
}

/* A token is issued only when the coalition sample is bracketed by the same
 * kernel process incarnation. Kernel signalling compares the PID version too.
 * The token is an identity guard; it does not grant signal permissions. */
static int sosix_darwin_coalition_member_token(pid_t pid, uint64_t coalition,
        audit_token_t *token) {
    if (pid <= 1 || !coalition || !token) return EINVAL;
    SosixDarwinProcessIdentity before, after;
    SosixDarwinCoalitionInfo info;
    int e = sosix_darwin_coalition_identity(pid, &before, 0);
    if (!e) e = sosix_darwin_coalition_info(pid, &info);
    if (!e) e = sosix_darwin_coalition_identity(pid, &after, 0);
    if (e) return e;
    if (before.unique_id != after.unique_id || before.pid_version != after.pid_version)
        return EAGAIN;
    if (info.ids[0] != coalition) return EXDEV;
    memset(token, 0, sizeof(*token));
    token->val[5] = (uint32_t)pid;
    token->val[7] = (uint32_t)after.pid_version;
    return 0;
}

static int sosix_darwin_coalition_signal(audit_token_t *token, int signal_number) {
    typedef int (*SignalFn)(audit_token_t *, int);
    SignalFn signal_fn = (SignalFn)dlsym(RTLD_DEFAULT, "proc_signal_with_audittoken");
    if (!signal_fn) return ENOTSUP;
    int e = signal_fn(token, signal_number);
    return e < 0 ? (errno ? errno : EIO) : e;
}

static int sosix_darwin_coalition_counts(uint64_t coalition, uint64_t *started,
        uint64_t *exited) {
    typedef int (*UsageFn)(uint64_t, void *, size_t);
    UsageFn usage_fn = (UsageFn)dlsym(RTLD_DEFAULT, "coalition_info_resource_usage");
    if (!usage_fn) return ENOTSUP;
    /* The kernel accepts the stable two-field prefix and bounds copyout. */
    uint64_t counters[2] = {0, 0};
    if (usage_fn(coalition, counters, sizeof(counters))) return errno ? errno : EIO;
    if (counters[1] > counters[0]) return EPROTO;
    *started = counters[0]; *exited = counters[1]; return 0;
}

static int64_t sosix_darwin_coalition_now_ns(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) return -1;
    return (int64_t)t.tv_sec * 1000000000LL + t.tv_nsec;
}

static int sosix_darwin_coalition_check_deadline(int64_t deadline) {
    int64_t now = sosix_darwin_coalition_now_ns();
    return now < 0 ? EIO : now >= deadline ? ETIMEDOUT : 0;
}

/* Bounded full census. A full buffer never means a complete process list. */
static int sosix_darwin_coalition_pids(pid_t **out, size_t *count) {
    size_t capacity = 1024;
    while (capacity <= 65536) {
        pid_t *pids = malloc(capacity * sizeof(*pids));
        if (!pids) return ENOMEM;
        int n = proc_listpids(PROC_ALL_PIDS, 0, pids, (int)(capacity * sizeof(*pids)));
        if (n <= 0) { int e = errno ? errno : EIO; free(pids); return e; }
        if ((size_t)n < capacity * sizeof(*pids)) {
            if ((size_t)n % sizeof(*pids)) { free(pids); return EPROTO; }
            *out = pids; *count = (size_t)n / sizeof(*pids); return 0;
        }
        free(pids); capacity *= 2;
    }
    return EOVERFLOW;
}

/* Admission must already be closed by the broker. An empty census does not
 * prove retirement: only the kernel coalition task counters do. Deadline or
 * an inaccessible member fails closed. The caller must separately prove reap.
 */
static int sosix_darwin_coalition_retire(uint64_t coalition, int64_t timeout_ns,
        SosixDarwinCoalitionRetirement *receipt) {
    if (!coalition || !receipt || timeout_ns <= 0 || timeout_ns > 30000000000LL)
        return EINVAL;
    memset(receipt, 0, sizeof(*receipt));
    int64_t start = sosix_darwin_coalition_now_ns();
    if (start < 0 || start > INT64_MAX - timeout_ns) return EIO;
    int64_t deadline = start + timeout_ns;
    SosixDarwinCoalitionInfo own;
    int e = sosix_darwin_coalition_info(getpid(), &own);
    if (e) return e;
    /* Never turn an untrusted ID into self/session-wide termination. */
    if (coalition == own.ids[0] || coalition <= 1) return EPERM;
    e = sosix_darwin_coalition_counts(coalition, &receipt->started, &receipt->exited);
    if (e) return e; /* Unknown IDs are not successful empty containers. */
    for (;;) {
        e = sosix_darwin_coalition_check_deadline(deadline); if (e) return e;
        if (receipt->started == receipt->exited) { receipt->tasks_empty = 1; return 0; }
        pid_t *pids = NULL; size_t count = 0;
        e = sosix_darwin_coalition_pids(&pids, &count); if (e) return e;
        e = sosix_darwin_coalition_check_deadline(deadline);
        if (e) { free(pids); return e; }
        receipt->passes++;
        SOSIX_DARWIN_COALITION_AFTER_CENSUS();
        for (size_t i = 0; i < count; i++) {
            e = sosix_darwin_coalition_check_deadline(deadline);
            if (e) { free(pids); return e; }
            if (pids[i] <= 1 || pids[i] == getpid()) continue;
            audit_token_t token;
            e = sosix_darwin_coalition_member_token(pids[i], coalition, &token);
            if (e == ESRCH || e == EAGAIN || e == EXDEV) continue;
            if (e) { free(pids); return e; }
            e = sosix_darwin_coalition_check_deadline(deadline);
            if (e) { free(pids); return e; }
            e = sosix_darwin_coalition_signal(&token, SIGKILL);
            if (e && e != ESRCH) { free(pids); return e; }
            if (!e) receipt->signal_count++;
        }
        free(pids);
        e = sosix_darwin_coalition_counts(coalition, &receipt->started, &receipt->exited);
        /* Deallocation requires kernel-empty + launchd coalition reap. We
         * retain the last observed counters; do not invent exit totals. */
        if (e == ESRCH) {
            e = sosix_darwin_coalition_check_deadline(deadline); if (e) return e;
            receipt->tasks_empty = 1; return 0;
        }
        if (e) return e;
        struct timespec delay = {0, 1000000}; nanosleep(&delay, NULL);
    }
}
#endif
#endif
