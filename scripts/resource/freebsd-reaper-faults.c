/* Focused test interposer only; never linked into the production helper.
 * clang -shared -fPIC freebsd-reaper-faults.c -o <owned-build>/reaper-faults.so
 * The marker is owned by the test harness and is removed to release a fault. */
#include <sys/types.h>
#include <sys/procctl.h>
#include <sys/sysctl.h>
#include <sys/user.h>
#include <sys/proc.h>
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static int identity(pid_t pid, long long sec, long usec, struct kinfo_proc *p) {
    int mib[] = {CTL_KERN, KERN_PROC, KERN_PROC_PID, pid};
    size_t size = sizeof(*p);
    memset(p, 0, sizeof(*p));
    if (sysctl(mib, 4, p, &size, NULL, 0) || size != sizeof(*p) ||
        p->ki_structsize != sizeof(*p) || p->ki_pid != pid ||
        p->ki_start.tv_sec != sec || p->ki_start.tv_usec != usec) return 0;
    return 1;
}

/* Hold the first real list after command-loop draining. The harness releases
 * an identified nested owner only after entered exists; state, not elapsed
 * sleep, proves its zombie transition and retained live subtree. */
static int zombie_barrier(const char *marker, struct procctl_reaper_pids *list,
    int (*real_procctl)(idtype_t, id_t, int, void *)) {
    char entered[4096], observed[4096];
    int target, leaf;
    long long target_sec, leaf_sec;
    long target_usec, leaf_usec;
    FILE *input = fopen(marker, "r");
    if (!input) return -1;
    int fields = fscanf(input, "%d %lld %ld %d %lld %ld", &target, &target_sec,
        &target_usec, &leaf, &leaf_sec, &leaf_usec);
    fclose(input);
    if (fields != 6 || target <= 0 || leaf <= 0 || target == leaf ||
        snprintf(entered, sizeof(entered), "%s.entered", marker) >= (int)sizeof(entered) ||
        snprintf(observed, sizeof(observed), "%s.observed", marker) >= (int)sizeof(observed)) {
        errno = EINVAL; return -1;
    }
    int found = 0;
    for (unsigned i = 0; i < list->rp_count; ++i) {
        if (!(list->rp_pids[i].pi_flags & REAPER_PIDINFO_VALID)) break;
        if (list->rp_pids[i].pi_pid == target &&
            (list->rp_pids[i].pi_flags & REAPER_PIDINFO_REAPER)) found = 1;
    }
    struct kinfo_proc before, zombie, child;
    if (!found || !identity(target, target_sec, target_usec, &before) || before.ki_stat == SZOMB) {
        errno = EPROTO; return -1;
    }
    FILE *ready = fopen(entered, "wx");
    if (!ready) return -1;
    if (fclose(ready)) return -1;
    struct timespec start, now;
    if (clock_gettime(CLOCK_MONOTONIC, &start)) return -1;
    for (;;) {
        if (!identity(target, target_sec, target_usec, &zombie)) { errno = EPROTO; return -1; }
        if (zombie.ki_stat == SZOMB) break;
        if (clock_gettime(CLOCK_MONOTONIC, &now)) return -1;
        double elapsed = now.tv_sec - start.tv_sec + (now.tv_nsec - start.tv_nsec) / 1e9;
        if (elapsed >= 2.0) { errno = ETIMEDOUT; return -1; }
        struct timespec delay = {0, 1000000};
        nanosleep(&delay, NULL);
    }
    struct procctl_reaper_status status = {0};
    if (!identity(leaf, leaf_sec, leaf_usec, &child) || child.ki_stat == SZOMB ||
        real_procctl(P_PID, leaf, PROC_REAP_STATUS, &status) ||
        status.rs_reaper != target || (status.rs_flags & REAPER_STATUS_OWNED) ||
        !identity(leaf, leaf_sec, leaf_usec, &child) || child.ki_stat == SZOMB) {
        errno = EPROTO; return -1;
    }
    long page = sysconf(_SC_PAGESIZE);
    if (page <= 0 || page % 1024 || child.ki_rssize < 0) { errno = EPROTO; return -1; }
    FILE *out = fopen(observed, "wx");
    if (!out) return -1;
    int written = fprintf(out, "%d %lld %ld %d %lld %ld %llu %d\n", target, target_sec,
        target_usec, leaf, leaf_sec, leaf_usec,
        (unsigned long long)child.ki_rssize * (page / 1024), status.rs_reaper);
    int closed = fclose(out);
    if (written < 0 || closed || unlink(marker)) return -1;
    return 0;
}

int procctl(idtype_t type, id_t id, int command, void *data) {
    static int (*real_procctl)(idtype_t, id_t, int, void *);
    if (!real_procctl) real_procctl = dlsym(RTLD_NEXT, "procctl");
    if (!real_procctl) { errno = ENOSYS; return -1; }
    const char *marker = getenv("SIMPLE_REAPER_FAULT_MARKER");
    const char *mode = getenv("SIMPLE_REAPER_FAULT_MODE");
    if (type == P_PID && (id == 0 || id == (id_t)getpid()) && marker && mode &&
        access(marker, F_OK) == 0) {
        if (!strcmp(mode, "zombie-barrier") && command == PROC_REAP_GETPIDS) {
            int result = real_procctl(type, id, command, data);
            return result ? result : zombie_barrier(marker, data, real_procctl);
        }
        if ((!strcmp(mode, "cleanup-denied") && command == PROC_REAP_KILL) ||
            (!strcmp(mode, "query-denied") && command == PROC_REAP_GETPIDS)) {
            errno = EPERM;
            return -1;
        }
        if (!strcmp(mode, "query-full") && command == PROC_REAP_GETPIDS) {
            struct procctl_reaper_pids *p = data;
            if (!p || !p->rp_pids || p->rp_count > 16385) { errno = EINVAL; return -1; }
            memset(p->rp_pids, 0, p->rp_count * sizeof(*p->rp_pids));
            for (unsigned i = 0; i < p->rp_count; ++i) {
                p->rp_pids[i].pi_flags = REAPER_PIDINFO_VALID;
                p->rp_pids[i].pi_pid = getpid();
            }
            return 0;
        }
    }
    return real_procctl(type, id, command, data);
}
