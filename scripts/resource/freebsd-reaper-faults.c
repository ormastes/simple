/* Focused test interposer only; never linked into the production helper.
 * clang -shared -fPIC freebsd-reaper-faults.c -o <owned-build>/reaper-faults.so
 * The marker is owned by the test harness and is removed to release a fault. */
#include <sys/types.h>
#include <sys/procctl.h>
#include <dlfcn.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int procctl(idtype_t type, id_t id, int command, void *data) {
    static int (*real_procctl)(idtype_t, id_t, int, void *);
    if (!real_procctl) real_procctl = dlsym(RTLD_NEXT, "procctl");
    if (!real_procctl) { errno = ENOSYS; return -1; }
    const char *marker = getenv("SIMPLE_REAPER_FAULT_MARKER");
    const char *mode = getenv("SIMPLE_REAPER_FAULT_MODE");
    if (type == P_PID && (id == 0 || id == (id_t)getpid()) && marker && mode &&
        access(marker, F_OK) == 0) {
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
