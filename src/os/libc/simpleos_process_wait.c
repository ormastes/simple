/*
 * SimpleOS process-wait wrappers — waitpid, wait, popen, pclose, system
 *
 * waitpid delegates to the canonical IF-01 syscall wrapper in simpleos_fork.c.
 * popen/pclose/system remain process-composition helpers and fail with ENOSYS
 * until fork/exec/pipe are fully implemented by the kernel.
 */

#include <sys/types.h>
#include <sys/wait.h>
#include <stdio.h>
#include <errno.h>

extern pid_t simpleos_waitpid(pid_t pid, int *wstatus, int options);

pid_t waitpid(pid_t pid, int *wstatus, int options) {
    return simpleos_waitpid(pid, wstatus, options);
}

pid_t wait(int *wstatus) {
    return waitpid((pid_t)-1, wstatus, 0);
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
