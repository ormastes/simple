#ifndef __APPLE__
#include <stdio.h>
int main(void) { puts("SKIP: Darwin UID zombie barrier requires macOS"); return 77; }
#else
#define _DARWIN_C_SOURCE
#include <sys/types.h>
#include <sys/sysctl.h>
#include <assert.h>
#include <stdio.h>
#include <sys/wait.h>
#include <unistd.h>
#include <errno.h>
static int test_sysctl(int *, unsigned, void *, size_t *, void *, size_t);
static void after_snapshot(void);
#define SOSIX_DARWIN_UID_PROCESS_SYSCTL test_sysctl
#define SOSIX_DARWIN_UID_PROCESS_AFTER_SNAPSHOT() after_snapshot()
#include "../runtime_sosix_darwin_uid_process_private.h"

static int inject_permission, inject_short, inject_delay;
static int resize_count;
static pid_t reap_after_snapshot;
static pid_t transitional_record;
static int transitional_observed;

static int test_sysctl(int *mib, unsigned count, void *out, size_t *size, void *value, size_t length) {
    if (inject_permission) { errno = EACCES; return -1; }
    if (out && inject_short) { inject_short--; resize_count++; errno = ENOMEM; return -1; }
    int e = sysctl(mib, count, out, size, value, length);
    if (!e && out && transitional_record) {
        struct kinfo_proc *records = out;
        int found = 0;
        for (size_t i = 0; i < *size / sizeof(*records); i++) {
            if (records[i].kp_proc.p_pid != transitional_record) continue;
            records[0] = records[i]; records[0].kp_proc.p_stat = SRUN;
            *size = sizeof(*records); found = transitional_observed = 1; break;
        }
        assert(found);
    }
    return e;
}

static void after_snapshot(void) {
    if (inject_delay) {
        inject_delay = 0; struct timespec delay = {0, 100000000}; nanosleep(&delay, NULL);
    }
    if (reap_after_snapshot) {
        assert(waitpid(reap_after_snapshot, NULL, 0) == reap_after_snapshot);
        reap_after_snapshot = 0;
    }
}

static pid_t make_zombie(uint64_t *identity) {
    int go[2]; assert(!pipe(go));
    pid_t child = fork(); assert(child >= 0);
    if (!child) {
        alarm(10); close(go[1]); char byte;
        assert(read(go[0], &byte, 1) == 1); _exit(0);
    }
    close(go[0]); SosixDarwinProcessIdentity info;
    assert(!sosix_darwin_coalition_identity(child, &info, 0));
    *identity = info.unique_id;
    assert(write(go[1], "X", 1) == 1); close(go[1]);
    siginfo_t status; memset(&status, 0, sizeof(status));
    assert(!waitid(P_PID, child, &status, WEXITED | WNOWAIT));
    return child;
}

static void live_record_case(void) {
    int release[2]; assert(!pipe(release));
    pid_t child = fork(); assert(child >= 0);
    if (!child) {
        alarm(10); close(release[1]); char command;
        assert(read(release[0], &command, 1) == 1); _exit(0);
    }
    close(release[0]); SosixDarwinProcessIdentity identity;
    assert(!sosix_darwin_coalition_identity(child, &identity, 0));
    SosixDarwinUidProcessObservation observation;
    assert(sosix_darwin_uid_process_barrier(getuid(), identity.unique_id, 10000000,
        &observation) == ETIMEDOUT);
    assert(observation.blocking_processes && !observation.no_new_uid_processes);
    assert(write(release[1], "R", 1) == 1); close(release[1]);
    assert(waitpid(child, NULL, 0) == child);
    assert(!sosix_darwin_uid_process_barrier(getuid(), identity.unique_id, 1000000000, &observation));
    assert(observation.no_new_uid_processes);
    puts("new_live_uid_record: blocks_until_reaped");
}

static void unobserved_descendant_case(void) {
    int ready[2], release[2]; assert(!pipe(ready) && !pipe(release));
    pid_t root = fork(); assert(root >= 0);
    if (!root) {
        alarm(10); close(ready[0]); close(release[1]);
        pid_t child = fork(); assert(child >= 0);
        if (!child) { alarm(10); assert(setsid() == getpid()); _exit(0); }
        siginfo_t info; memset(&info, 0, sizeof(info));
        assert(!waitid(P_PID, child, &info, WEXITED | WNOWAIT));
        assert(write(ready[1], "Z", 1) == 1);
        char command; assert(read(release[0], &command, 1) == 1);
        assert(waitpid(child, NULL, 0) == child); _exit(0);
    }
    close(ready[1]); close(release[0]);
    SosixDarwinProcessIdentity identity;
    assert(!sosix_darwin_coalition_identity(root, &identity, 0));
    char status; assert(read(ready[0], &status, 1) == 1 && status == 'Z');
    close(ready[0]);
    /* The observer was never told the descendant PID and cannot waitpid it. */
    SosixDarwinUidProcessObservation observation;
    assert(sosix_darwin_uid_process_barrier(getuid(), identity.unique_id, 10000000,
        &observation) == ETIMEDOUT);
    assert(observation.blocking_processes && !observation.no_new_uid_processes);
    assert(write(release[1], "R", 1) == 1); close(release[1]);
    assert(waitpid(root, NULL, 0) == root);
    assert(!sosix_darwin_uid_process_barrier(getuid(), identity.unique_id, 1000000000, &observation));
    assert(observation.no_new_uid_processes);
    puts("unobserved_session_descendant_zombie: blocks_until_reaped");
}

int main(void) {
    alarm(20);
    uint64_t old_id, new_id;
    pid_t old = make_zombie(&old_id);
    pid_t fresh = make_zombie(&new_id);
    assert(new_id > old_id);
    SosixDarwinUidProcessObservation observation;
    assert(sosix_darwin_uid_process_barrier(getuid(), new_id, 10000000, &observation) == ETIMEDOUT);
    assert(observation.blocking_processes >= 1 && !observation.no_new_uid_processes);
    puts("new_unreaped_uid_process: blocks");

    /* Model P_REF_DEAD/non-SZOMB with a real retained process identity. */
    transitional_record = fresh;
    assert(sosix_darwin_uid_process_barrier(getuid(), new_id, 10000000, &observation) == ETIMEDOUT);
    assert(transitional_observed && observation.blocking_processes == 1 && !observation.no_new_uid_processes);
    transitional_record = 0;
    puts("non_zombie_exit_transition: blocks");
    live_record_case();

    /* Force a census resize while a genuine zombie remains. */
    inject_short = 1;
    assert(sosix_darwin_uid_process_barrier(getuid(), new_id, 10000000, &observation) == ETIMEDOUT);
    assert(resize_count == 1 && !observation.no_new_uid_processes);
    puts("short_census: retried_without_false_absence");

    inject_permission = 1;
    assert(sosix_darwin_uid_process_barrier(getuid(), new_id, 10000000, &observation) == EACCES);
    assert(!observation.no_new_uid_processes); inject_permission = 0;
    puts("census_permission_failure: closed");

    /* Reaping after the snapshot is safe: ESRCH means that sampled zombie is
     * gone. No polling race may turn a retained zombie into a success. */
    reap_after_snapshot = fresh;
    assert(!sosix_darwin_uid_process_barrier(getuid(), new_id, 1000000000, &observation));
    assert(observation.no_new_uid_processes && !reap_after_snapshot);
    SosixDarwinProcessIdentity still_old;
    assert(!sosix_darwin_coalition_identity(old, &still_old, 1));
    assert(still_old.unique_id == old_id);
    puts("old_unrelated_zombie: excluded_by_kernel_unique_id");
    puts("reaped_after_snapshot: safely_resolved");

    inject_delay = 1;
    assert(sosix_darwin_uid_process_barrier(getuid(), new_id, 10000000, &observation) == ETIMEDOUT);
    assert(!observation.no_new_uid_processes);
    puts("post_snapshot_deadline: closed");
    assert(waitpid(old, NULL, 0) == old);
    unobserved_descendant_case();
    puts("generic_reap_capability: not_claimed");
    puts("darwin_uid_process_barrier: pass");
    return 0;
}
#endif
