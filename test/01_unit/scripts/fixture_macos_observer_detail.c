/* Deterministic libproc transition/failure seam. Production code has no
 * environment bypass and is compiled unchanged into this translation unit. */
#include <sys/types.h>
#include <libproc.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
static int fake_pidinfo(int, int, uint64_t, void *, int);
static pid_t fake_getsid(pid_t);
#define proc_pidinfo fake_pidinfo
#define getsid fake_getsid
#define main observer_main
#include "../../../scripts/resource/macos-process-observer.c"
#undef main
#undef proc_pidinfo
#undef getsid

static const char *mode;
static int bsd_calls;

static int fake_pidinfo(int pid, int flavor, uint64_t arg, void *buffer, int size) {
    (void)pid; (void)arg;
    const char *stage = flavor == PROC_PIDTASKINFO ? "task" :
        ++bsd_calls == 1 ? "bsd-before" : "bsd-after";
    if (!strcmp(mode, stage)) { errno = EIO; return 0; }
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
    if (!strcmp(mode, "gone-session")) { errno = ESRCH; return -1; }
    return 123;
}

int main(int argc, char **argv) {
    if (argc != 2) return 64;
    mode = argv[1];
    return detail(123, 100, 42) ? 89 : 0;
}
