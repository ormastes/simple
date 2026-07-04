/*
 * SimpleOS process-wait wrappers — waitpid, wait, popen, pclose, system
 *
 * waitpid delegates to the canonical IF-01 syscall wrapper in simpleos_fork.c.
 * popen/pclose/system remain process-composition helpers and fail with ENOSYS
 * until fork/exec/pipe are fully implemented by the kernel.
 */

#include <sys/types.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <stdio.h>
#include <errno.h>

extern pid_t simpleos_waitpid(pid_t pid, int *wstatus, int options);

pid_t waitpid(pid_t pid, int *wstatus, int options) {
    return simpleos_waitpid(pid, wstatus, options);
}

pid_t wait(int *wstatus) {
    return waitpid((pid_t)-1, wstatus, 0);
}

pid_t wait4(pid_t pid, int *wstatus, int options, struct rusage *usage) {
    if (usage) {
        usage->ru_utime.tv_sec = 0;
        usage->ru_utime.tv_usec = 0;
        usage->ru_stime.tv_sec = 0;
        usage->ru_stime.tv_usec = 0;
        usage->ru_maxrss = 0;
    }
    return waitpid(pid, wstatus, options);
}

FILE *popen(const char *command, const char *type) {
    (void)command; (void)type;
    errno = ENOSYS;
    return NULL;
}

int pclose(FILE *stream) {
    (void)stream;
    errno = ECHILD;
    return -1;
}

int system(const char *command) {
    if (!command) return 0;
    errno = ENOSYS;
    return -1;
}

int getrusage(int who, struct rusage *usage) {
    (void)who;
    if (usage) {
        usage->ru_utime.tv_sec = 0;
        usage->ru_utime.tv_usec = 0;
        usage->ru_stime.tv_sec = 0;
        usage->ru_stime.tv_usec = 0;
        usage->ru_maxrss = 0;
    }
    return 0;
}

int getrlimit(int resource, struct rlimit *rlim) {
    if (resource != RLIMIT_DATA && resource != RLIMIT_STACK && resource != RLIMIT_CORE) {
        errno = EINVAL;
        return -1;
    }
    if (rlim) {
        rlim->rlim_cur = RLIM_INFINITY;
        rlim->rlim_max = RLIM_INFINITY;
    }
    return 0;
}

int setrlimit(int resource, const struct rlimit *rlim) {
    (void)rlim;
    if (resource != RLIMIT_DATA && resource != RLIMIT_STACK && resource != RLIMIT_CORE) {
        errno = EINVAL;
        return -1;
    }
    return 0;
}
