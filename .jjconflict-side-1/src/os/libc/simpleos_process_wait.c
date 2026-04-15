/*
 * SimpleOS process-wait stubs — waitpid, wait, popen, pclose, system
 *
 * SimpleOS is a single-process exokernel: no fork, no child processes.
 * These stubs return sensible "not supported" values so the linker resolves
 * and callers fail loudly instead of silently deadlocking.
 */

#include <sys/types.h>
#include <stdio.h>
#include <errno.h>

#ifndef WNOHANG
#define WNOHANG   1
#endif

pid_t waitpid(pid_t pid, int *wstatus, int options) {
    (void)pid; (void)options;
    if (wstatus) *wstatus = 0;
    errno = ECHILD;
    return -1;
}

pid_t wait(int *wstatus) {
    if (wstatus) *wstatus = 0;
    errno = ECHILD;
    return -1;
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
