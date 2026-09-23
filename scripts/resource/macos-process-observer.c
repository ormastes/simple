/* Bootstrap-only syscall observer. Policy and containment stay in the Perl
 * supervisor. One persistent process avoids executable admission per sample;
 * KERN_PROC_ALL supplies identities without querying every host task's RSS. */
#define _DARWIN_C_SOURCE
#include <sys/types.h>
#include <sys/sysctl.h>
#include <sys/proc.h>
#include <libproc.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <time.h>
#include <mach/mach_time.h>

static int detail_failure(const char *operation, int pid, int bytes,
                          unsigned long long sec, unsigned long long usec) {
    int error = errno;
    if (error == EPERM || error == EACCES) {
        /* A libproc permission error is not evidence of exit. Independently
         * check kernel PID metadata: only a missing PID or the exact expected
         * zombie can be omitted. Live/reused/unknown state still fails closed. */
        struct kinfo_proc proof;
        size_t size = sizeof(proof);
        int mib[] = { CTL_KERN, KERN_PROC, KERN_PROC_PID, pid };
        int result = sysctl(mib, 4, &proof, &size, NULL, 0);
        if (!result && !size) return printf("R %d gone\n", pid) < 0;
        if (!result && size == sizeof(proof) && proof.kp_proc.p_pid == pid &&
            (unsigned long long)proof.kp_proc.p_starttime.tv_sec == sec &&
            (unsigned long long)proof.kp_proc.p_starttime.tv_usec == usec &&
            proof.kp_proc.p_stat == SZOMB) return printf("R %d gone\n", pid) < 0;
        if (!result && size == sizeof(proof)) {
            fprintf(stderr, "macos-process-observer: denial-state pid=%d observed_pid=%d state=%d expected=%llu:%llu actual=%llu:%llu\n",
                    pid, proof.kp_proc.p_pid, proof.kp_proc.p_stat, sec, usec,
                    (unsigned long long)proof.kp_proc.p_starttime.tv_sec,
                    (unsigned long long)proof.kp_proc.p_starttime.tv_usec);
            char command[sizeof(proof.kp_proc.p_comm) + 1];
            size_t i;
            for (i = 0; i < sizeof(proof.kp_proc.p_comm) && proof.kp_proc.p_comm[i]; ++i) {
                unsigned char c = (unsigned char)proof.kp_proc.p_comm[i];
                command[i] = c > 32 && c < 127 ? (char)c : '_';
            }
            command[i] = 0;
            pid_t sid = getsid(pid);
            fprintf(stderr, "macos-process-observer: denial-owner pid=%d ppid=%d pgid=%d sid=%d uid=%u ruid=%u command=%s\n",
                    pid, proof.kp_eproc.e_ppid, proof.kp_eproc.e_pgid, sid,
                    proof.kp_eproc.e_ucred.cr_uid, proof.kp_eproc.e_pcred.p_ruid, command);
        }
        fprintf(stderr, "macos-process-observer: denial-proof pid=%d result=%d bytes=%zu errno=%d\n",
                pid, result, size, result ? errno : 0);
    }
    fprintf(stderr, "macos-process-observer: %s pid=%d bytes=%d errno=%d\n",
            operation, pid, bytes, error);
    return 1;
}

static int identity_failure(const char *operation, int pid,
                            unsigned long long sec, unsigned long long usec,
                            const struct proc_bsdinfo *actual) {
    fprintf(stderr, "macos-process-observer: %s pid=%d expected=%llu:%llu actual=%llu:%llu\n",
            operation, pid, sec, usec, (unsigned long long)actual->pbi_start_tvsec,
            (unsigned long long)actual->pbi_start_tvusec);
    return 1;
}

static int metadata(void) {
    int mib[] = { CTL_KERN, KERN_PROC, KERN_PROC_ALL, 0 };
    struct kinfo_proc *rows = NULL;
    size_t bytes = 0;
    /* The process table can grow between size and data calls. Bound retries
     * and memory; the supervisor also bounds the entire request's duration. */
    for (int attempt = 0; attempt < 3; ++attempt) {
        if (sysctl(mib, 4, NULL, &bytes, NULL, 0)) return 1;
        if (bytes > 64 * 1024 * 1024) return 1;
        bytes += 64 * sizeof(*rows);
        rows = malloc(bytes);
        if (!rows) return 1;
        if (!sysctl(mib, 4, rows, &bytes, NULL, 0)) break;
        int error = errno;
        free(rows); rows = NULL;
        if (error != ENOMEM) return 1;
    }
    if (!rows || bytes % sizeof(*rows)) { free(rows); return 1; }
    for (size_t i = 0; i < bytes / sizeof(*rows); ++i) {
        const struct kinfo_proc *p = rows + i;
        if (p->kp_proc.p_pid <= 0) continue;
        printf("M %d %d %d %d %llu:%llu\n", p->kp_proc.p_pid,
               p->kp_eproc.e_ppid, p->kp_eproc.e_pgid,
               p->kp_proc.p_stat == SZOMB,
               (unsigned long long)p->kp_proc.p_starttime.tv_sec,
               (unsigned long long)p->kp_proc.p_starttime.tv_usec);
    }
    free(rows);
    return puts("E") == EOF || fflush(stdout);
}

static int detail(int pid, unsigned long long sec, unsigned long long usec) {
    struct proc_bsdinfo before, after;
    struct proc_taskinfo task;
    errno = 0;
    int n = proc_pidinfo(pid, PROC_PIDTBSDINFO, 0, &before, sizeof(before));
    if (!n && errno == ESRCH) return printf("R %d gone\n", pid) < 0;
    if (n != sizeof(before)) return detail_failure("bsd-before", pid, n, sec, usec);
    if (before.pbi_start_tvsec != sec || before.pbi_start_tvusec != usec)
        return identity_failure("identity-before", pid, sec, usec, &before);
    if (before.pbi_status == SZOMB) return printf("R %d gone\n", pid) < 0;
    errno = 0;
    n = proc_pidinfo(pid, PROC_PIDTASKINFO, 0, &task, sizeof(task));
    if (!n && errno == ESRCH) return printf("R %d gone\n", pid) < 0;
    if (n != sizeof(task)) return detail_failure("task", pid, n, sec, usec);
    errno = 0;
    pid_t sid = getsid(pid);
    if (sid < 0 && errno == ESRCH) return printf("R %d gone\n", pid) < 0;
    if (sid < 0) return detail_failure("session", pid, sid, sec, usec);
    errno = 0;
    n = proc_pidinfo(pid, PROC_PIDTBSDINFO, 0, &after, sizeof(after));
    if (!n && errno == ESRCH) return printf("R %d gone\n", pid) < 0;
    if (n != sizeof(after)) return detail_failure("bsd-after", pid, n, sec, usec);
    if (after.pbi_start_tvsec != sec || after.pbi_start_tvusec != usec)
        return identity_failure("identity-after", pid, sec, usec, &after);
    return printf("R %d %llu %d\n", pid,
                  (unsigned long long)((task.pti_resident_size + 1023) / 1024), sid) < 0;
}

/* Progress reporting uses the same unprivileged syscalls as containment. Never
 * exec Darwin's setuid /bin/ps from inside the measured workload. The existing
 * M/R protocol remains unchanged; each progress request has a hard deadline. */
static int progress(int root, int identity_only) {
    alarm(5);
    if (geteuid() != getuid() || getegid() != getgid()) return 89;
    mach_timebase_info_data_t timebase;
    if (mach_timebase_info(&timebase) != KERN_SUCCESS || !timebase.denom) return 89;
    int mib[] = { CTL_KERN, KERN_PROC, KERN_PROC_ALL, 0 };
    struct kinfo_proc *rows = NULL;
    size_t bytes = 0;
    for (int attempt = 0; attempt < 3; ++attempt) {
        if (sysctl(mib, 4, NULL, &bytes, NULL, 0) || bytes > 64 * 1024 * 1024) return 89;
        bytes += 64 * sizeof(*rows);
        rows = malloc(bytes);
        if (!rows) return 89;
        if (!sysctl(mib, 4, rows, &bytes, NULL, 0)) break;
        int error = errno;
        free(rows); rows = NULL;
        if (error != ENOMEM) return 89;
    }
    if (!rows || bytes % sizeof(*rows)) { free(rows); return 89; }
    size_t count = bytes / sizeof(*rows), root_index = count;
    for (size_t i = 0; i < count; ++i)
        if (rows[i].kp_proc.p_pid == root) root_index = i;
    if (root_index == count) { free(rows); return 0; }
    if (identity_only) {
        const struct timeval *start = &rows[root_index].kp_proc.p_starttime;
        time_t seconds = start->tv_sec, elapsed = time(NULL) - seconds;
        char birth[64];
        struct tm local;
        if (!localtime_r(&seconds, &local) ||
            !strftime(birth, sizeof(birth), "%a %b %e %T %Y", &local)) { free(rows); return 89; }
        printf("%lld:%d %lld %s\n", (long long)seconds, start->tv_usec,
               (long long)(elapsed < 0 ? 0 : elapsed), birth);
        free(rows);
        return fflush(stdout) ? 89 : 0;
    }
    unsigned char *selected = calloc(count, 1);
    if (!selected) { free(rows); return 89; }
    selected[root_index] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (size_t i = 0; i < count; ++i) {
            if (selected[i]) continue;
            for (size_t j = 0; j < count; ++j)
                if (selected[j] && rows[i].kp_eproc.e_ppid == rows[j].kp_proc.p_pid) {
                    selected[i] = 1; changed = 1; break;
                }
        }
    }
    for (size_t i = 0; i < count; ++i) {
        const struct kinfo_proc *p = rows + i;
        if ((!selected[i] && p->kp_eproc.e_pgid != rows[root_index].kp_eproc.e_pgid) ||
            p->kp_proc.p_pid <= 0 || p->kp_proc.p_stat == SZOMB) continue;
        struct proc_taskinfo task;
        struct proc_bsdinfo after;
        errno = 0;
        int n = proc_pidinfo(p->kp_proc.p_pid, PROC_PIDTASKINFO, 0, &task, sizeof(task));
        if (!n && errno == ESRCH) continue;
        if (n != sizeof(task)) { free(selected); free(rows); return 89; }
        errno = 0;
        n = proc_pidinfo(p->kp_proc.p_pid, PROC_PIDTBSDINFO, 0, &after, sizeof(after));
        if (!n && errno == ESRCH) continue;
        if (n != sizeof(after) || after.pbi_start_tvsec != (uint64_t)p->kp_proc.p_starttime.tv_sec ||
            after.pbi_start_tvusec != (uint64_t)p->kp_proc.p_starttime.tv_usec) {
            free(selected); free(rows); return 89;
        }
        char name[sizeof(p->kp_proc.p_comm) + 1];
        size_t j;
        for (j = 0; j < sizeof(p->kp_proc.p_comm) && p->kp_proc.p_comm[j]; ++j) {
            unsigned char c = p->kp_proc.p_comm[j];
            name[j] = c > 32 && c < 127 ? (char)c : '_';
        }
        name[j] = 0;
        /* Five birth fields preserve the shared BSD snapshot parser, while
         * retaining microseconds instead of ps's second-resolution identity. */
        printf("%d %d %d %llu %llu:%llu _ _ _ _ %.9f %s\n", p->kp_proc.p_pid,
               after.pbi_ppid, after.pbi_pgid,
               (unsigned long long)((task.pti_resident_size + 1023) / 1024),
               (unsigned long long)after.pbi_start_tvsec, (unsigned long long)after.pbi_start_tvusec,
               ((double)task.pti_total_user + (double)task.pti_total_system) *
                   timebase.numer / timebase.denom / 1e9,
               name[0] ? name : "unknown");
    }
    free(selected); free(rows);
    return fflush(stdout) ? 89 : 0;
}

int main(int argc, char **argv) {
    if (argc != 1) {
        char *end;
        if (argc != 3 || (strcmp(argv[1], "--progress") && strcmp(argv[1], "--identity"))) return 89;
        long pid = strtol(argv[2], &end, 10);
        if (*end || pid <= 0 || pid > INT32_MAX) return 89;
        return progress((int)pid, !strcmp(argv[1], "--identity"));
    }
    char line[128], extra;
    while (fgets(line, sizeof(line), stdin)) {
        int pid;
        unsigned long long sec, usec;
        if (!strcmp(line, "M\n")) {
            if (metadata()) return 89;
        } else if (sscanf(line, "R %d %llu:%llu %c", &pid, &sec, &usec, &extra) == 3 && pid > 0) {
            if (detail(pid, sec, usec) || fflush(stdout)) return 89;
        } else return 89;
    }
    return ferror(stdin) ? 89 : 0;
}
