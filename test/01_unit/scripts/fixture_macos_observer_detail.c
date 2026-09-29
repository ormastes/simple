/* Deterministic libproc transition/failure seam. Production code has no
 * environment bypass and is compiled unchanged into this translation unit. */
#include <sys/types.h>
#include <sys/sysctl.h>
#include <libproc.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
static int fake_pidinfo(int, int, uint64_t, void *, int);
static pid_t fake_getsid(pid_t);
static int fake_sysctl(int *, u_int, void *, size_t *, void *, size_t);
#define proc_pidinfo fake_pidinfo
#define getsid fake_getsid
#define sysctl fake_sysctl
#define main observer_main
#include "../../../scripts/resource/macos-process-observer.c"
#undef main
#undef proc_pidinfo
#undef getsid
#undef sysctl

static const char *mode;
static const char *proof_mode = "live";
static int bsd_calls;

static int fake_pidinfo(int pid, int flavor, uint64_t arg, void *buffer, int size) {
    (void)pid; (void)arg;
    const char *stage = flavor == PROC_PIDTASKINFO ? "task" :
        ++bsd_calls == 1 ? "bsd-before" : "bsd-after";
    if (!strcmp(mode, stage)) { errno = EIO; return 0; }
    if (!strncmp(mode, "denied-", 7) && !strcmp(mode + 7, stage)) {
        errno = EPERM; return 0;
    }
    if (!strncmp(mode, "gone-", 5) && !strcmp(mode + 5, stage)) {
        errno = ESRCH; return 0;
    }
    if (!strncmp(mode, "short-", 6) && !strcmp(mode + 6, stage)) return size - 1;
    memset(buffer, 0, (size_t)size);
    if (flavor == PROC_PIDTASKINFO) {
        ((struct proc_taskinfo *)buffer)->pti_resident_size = 4096;
    } else {
        struct proc_bsdinfo *b = buffer;
        b->pbi_start_tvsec = 100;
        b->pbi_start_tvusec = 42;
        if ((!strcmp(mode, "identity-before") && bsd_calls == 1) ||
            (!strcmp(mode, "identity-after") && bsd_calls == 2)) b->pbi_start_tvusec = 43;
        if (!strcmp(mode, "zombie")) b->pbi_status = SZOMB;
    }
    return size;
}

static pid_t fake_getsid(pid_t pid) {
    (void)pid;
    if (!strcmp(mode, "session")) { errno = EPERM; return -1; }
    if (!strcmp(mode, "denied-session")) { errno = EPERM; return -1; }
    if (!strcmp(mode, "gone-session")) { errno = ESRCH; return -1; }
    return 123;
}

static int fake_sysctl(int *mib, u_int count, void *buffer, size_t *size,
                       void *input, size_t input_size) {
    (void)input; (void)input_size;
    if (count != 4 || mib[0] != CTL_KERN || mib[1] != KERN_PROC ||
        mib[2] != KERN_PROC_PID || mib[3] != 123) abort();
    if (!strcmp(proof_mode, "denied")) { errno = EACCES; return -1; }
    if (!strcmp(proof_mode, "gone")) { *size = 0; return 0; }
    struct kinfo_proc *p = buffer;
    memset(p, 0, sizeof(*p));
    p->kp_proc.p_pid = !strcmp(proof_mode, "wrong-pid") ? 124 : 123;
    p->kp_proc.p_starttime.tv_sec = 100;
    p->kp_proc.p_starttime.tv_usec = !strcmp(proof_mode, "reused") ? 43 : 42;
    p->kp_proc.p_stat = !strcmp(proof_mode, "live") ? SRUN : SZOMB;
    memcpy(p->kp_proc.p_comm, "guard\ntest", 10);
    p->kp_eproc.e_ppid = 122;
    p->kp_eproc.e_pgid = 321;
    p->kp_eproc.e_ucred.cr_uid = 501;
    p->kp_eproc.e_pcred.p_ruid = 502;
    *size = sizeof(*p) - (!strcmp(proof_mode, "short") ? 1 : 0);
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 2 && argc != 3) return 64;
    mode = argv[1];
    if (argc == 3) proof_mode = argv[2];
    return detail(123, 100, 42) ? 89 : 0;
}
