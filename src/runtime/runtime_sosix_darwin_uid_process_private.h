/* Conservative UID BSD-process observation for a future trusted coalition broker.
 * This is not a generic reap capability. Its caller must first prove closed
 * admission, zero live coalition tasks, immutable descendant UID, and a genuine
 * root unique-id lower bound. Unrelated newer UID processes deliberately block.
 */
#ifndef RUNTIME_SOSIX_DARWIN_UID_PROCESS_PRIVATE_H
#define RUNTIME_SOSIX_DARWIN_UID_PROCESS_PRIVATE_H
#ifdef __APPLE__
#include "runtime_sosix_darwin_coalition_private.h"
#include <sys/sysctl.h>
#include <sys/proc.h>

#ifndef SOSIX_DARWIN_UID_PROCESS_SYSCTL
#define SOSIX_DARWIN_UID_PROCESS_SYSCTL sysctl
#endif
#ifndef SOSIX_DARWIN_UID_PROCESS_IDENTITY
#define SOSIX_DARWIN_UID_PROCESS_IDENTITY sosix_darwin_coalition_identity
#endif
#ifndef SOSIX_DARWIN_UID_PROCESS_AFTER_SNAPSHOT
#define SOSIX_DARWIN_UID_PROCESS_AFTER_SNAPSHOT() ((void)0)
#endif

typedef struct {
    uint64_t lower_unique_id;
    uid_t uid;
    size_t blocking_processes;
    unsigned scans;
    int no_new_uid_processes;
} SosixDarwinUidProcessObservation;

/* KERN_PROC snapshots use proc_iterate: allocation is rechecked while holding
 * the process-list lock, includes both active and zombie lists, and reports
 * ENOMEM instead of silently treating short user storage as a complete list.
 * proc_listpids' internal nprocs+20 allocation is unsuitable for this proof.
 */
static int sosix_darwin_uid_process_snapshot(uid_t uid, int64_t deadline,
        struct kinfo_proc **out, size_t *count) {
    if (!out || !count || uid > INT32_MAX) return EINVAL;
    *out = NULL; *count = 0;
    int mib[4] = {CTL_KERN, KERN_PROC, KERN_PROC_UID, (int)uid};
    for (int attempt = 0; attempt < 3; attempt++) {
        int e = sosix_darwin_coalition_check_deadline(deadline); if (e) return e;
        size_t bytes = 0;
        if (SOSIX_DARWIN_UID_PROCESS_SYSCTL(mib, 4, NULL, &bytes, NULL, 0))
            return errno ? errno : EIO;
        if (bytes > 32U * 1024U * 1024U) return EOVERFLOW;
        size_t capacity = bytes + 32 * sizeof(struct kinfo_proc);
        struct kinfo_proc *snapshot = malloc(capacity);
        if (!snapshot) return ENOMEM;
        bytes = capacity;
        if (SOSIX_DARWIN_UID_PROCESS_SYSCTL(mib, 4, snapshot, &bytes, NULL, 0)) {
            e = errno ? errno : EIO; free(snapshot);
            if (e == ENOMEM) continue;
            return e;
        }
        if (bytes > capacity || bytes % sizeof(*snapshot)) { free(snapshot); return EPROTO; }
        e = sosix_darwin_coalition_check_deadline(deadline);
        if (e) { free(snapshot); return e; }
        *out = snapshot; *count = bytes / sizeof(*snapshot); return 0;
    }
    return EAGAIN;
}

static int sosix_darwin_uid_process_barrier(uid_t uid, uint64_t lower_unique_id,
        int64_t timeout_ns, SosixDarwinUidProcessObservation *observation) {
    if (!observation || !lower_unique_id || lower_unique_id == UINT64_MAX ||
        uid > INT32_MAX || timeout_ns <= 0 || timeout_ns > 30000000000LL) return EINVAL;
    memset(observation, 0, sizeof(*observation));
    observation->uid = uid; observation->lower_unique_id = lower_unique_id;
    int64_t now = sosix_darwin_coalition_now_ns();
    if (now < 0 || now > INT64_MAX - timeout_ns) return EIO;
    int64_t deadline = now + timeout_ns;
    for (;;) {
        struct kinfo_proc *snapshot = NULL; size_t count = 0;
        int e = sosix_darwin_uid_process_snapshot(uid, deadline, &snapshot, &count);
        if (e) return e;
        observation->scans++; observation->blocking_processes = 0;
        SOSIX_DARWIN_UID_PROCESS_AFTER_SNAPSHOT();
        for (size_t i = 0; i < count; i++) {
            e = sosix_darwin_coalition_check_deadline(deadline);
            if (e) { free(snapshot); return e; }
            pid_t pid = snapshot[i].kp_proc.p_pid;
            if (pid <= 1) { free(snapshot); return EPROTO; }
            SosixDarwinProcessIdentity identity;
            e = SOSIX_DARWIN_UID_PROCESS_IDENTITY(pid, &identity, 1);
            /* A sampled record disappeared before identity lookup. A reused
             * PID can only have a newer unique-id, so conservatively block it.
             * Identity errors other than ESRCH never establish absence.
             * Count every BSD state: a task can leave its coalition before
             * proc_exit has changed the still-present record to SZOMB. */
            if (e == ESRCH) continue;
            if (e) { free(snapshot); return e; }
            if (!identity.unique_id) { free(snapshot); return EPROTO; }
            if (identity.unique_id >= lower_unique_id) observation->blocking_processes++;
        }
        free(snapshot);
        e = sosix_darwin_coalition_check_deadline(deadline); if (e) return e;
        if (!observation->blocking_processes) {
            observation->no_new_uid_processes = 1; return 0;
        }
        struct timespec delay = {0, 1000000}; nanosleep(&delay, NULL);
    }
}
#endif
#endif
