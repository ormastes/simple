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
    int n = proc_pidinfo(pid, PROC_PIDTBSDINFO, 0, &before, sizeof(before));
    if (!n && errno == ESRCH) return printf("R %d gone\n", pid) < 0;
    if (n != sizeof(before)) return 1;
    if (before.pbi_start_tvsec != sec || before.pbi_start_tvusec != usec)
        return 1; /* PID reuse is not an empty measurement. */
    if (before.pbi_status == SZOMB) return printf("R %d gone\n", pid) < 0;
    n = proc_pidinfo(pid, PROC_PIDTASKINFO, 0, &task, sizeof(task));
    if (!n && errno == ESRCH) return printf("R %d gone\n", pid) < 0;
    if (n != sizeof(task)) return 1;
    pid_t sid = getsid(pid);
    if (sid < 0 && errno == ESRCH) return printf("R %d gone\n", pid) < 0;
    if (sid < 0) return 1;
    n = proc_pidinfo(pid, PROC_PIDTBSDINFO, 0, &after, sizeof(after));
    if (!n && errno == ESRCH) return printf("R %d gone\n", pid) < 0;
    if (n != sizeof(after) || after.pbi_start_tvsec != sec ||
        after.pbi_start_tvusec != usec) return 1;
    return printf("R %d %llu %d\n", pid,
                  (unsigned long long)((task.pti_resident_size + 1023) / 1024), sid) < 0;
}

int main(void) {
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
