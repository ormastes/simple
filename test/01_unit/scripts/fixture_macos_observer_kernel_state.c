/* Real kernel process-state proof with an injected libproc EPERM. */
#include <sys/types.h>
#include <sys/wait.h>
#include <libproc.h>
#include <errno.h>
#include <string.h>
static int inject_denial = 1;
static int denied_pidinfo(int pid, int flavor, uint64_t arg, void *buf, int size) {
    if (!inject_denial) return proc_pidinfo(pid, flavor, arg, buf, size);
    (void)pid; (void)flavor; (void)arg; (void)buf; (void)size;
    errno = EPERM;
    return 0;
}
#define proc_pidinfo denied_pidinfo
#define main observer_main
#include "../../../scripts/resource/macos-process-observer.c"
#undef main
#undef proc_pidinfo

int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1], "--sandbox-denial")) {
        inject_denial = 0;
        int pid = getpid();
        int mib[] = { CTL_KERN, KERN_PROC, KERN_PROC_PID, pid };
        struct kinfo_proc p;
        size_t size = sizeof(p);
        if (sysctl(mib, 4, &p, &size, NULL, 0) || size != sizeof(p)) return 70;
        struct proc_bsdinfo b;
        errno = 0;
        int n = proc_pidinfo(pid, PROC_PIDTBSDINFO, 0, &b, sizeof(b));
        if (n != 0 || errno != EPERM) return 71;
        if (detail(pid, (unsigned long long)p.kp_proc.p_starttime.tv_sec,
                   (unsigned long long)p.kp_proc.p_starttime.tv_usec) != 1) return 72;
        puts("PASS: actual sandbox libproc EPERM remains fail-closed for live kernel identity");
        return 0;
    }
    if (argc != 1) return 64;
    int gate[2];
    if (pipe(gate)) return 70;
    pid_t pid = fork();
    if (pid < 0) return 70;
    if (!pid) { close(gate[1]); char byte; read(gate[0], &byte, 1); _exit(0); }
    close(gate[0]);
    int mib[] = { CTL_KERN, KERN_PROC, KERN_PROC_PID, pid };
    struct kinfo_proc p;
    size_t size = sizeof(p);
    if (sysctl(mib, 4, &p, &size, NULL, 0) || size != sizeof(p)) return 71;
    unsigned long long sec = (unsigned long long)p.kp_proc.p_starttime.tv_sec;
    unsigned long long usec = (unsigned long long)p.kp_proc.p_starttime.tv_usec;
    int live = detail(pid, sec, usec);
    close(gate[1]);
    siginfo_t info;
    if (waitid(P_PID, (id_t)pid, &info, WEXITED | WNOWAIT)) return 72;
    int zombie = detail(pid, sec, usec);
    int reuse = detail(pid, sec, usec + 1);
    if (waitpid(pid, NULL, 0) != pid) return 73;
    int gone = detail(pid, sec, usec);
    if (live != 1 || zombie != 0 || reuse != 1 || gone != 0) return 74;
    puts("PASS: real kernel live/zombie/gone states and mismatched identity under injected EPERM");
    return 0;
}
