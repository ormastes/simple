/*
 * SimpleOS fork/exec/waitpid — IF-01 syscall wrappers.
 *
 * These are normal user-space libc entrypoints. They use the same
 * simpleos_syscall trampoline as file I/O and memory operations, so C apps
 * can link against POSIX names while kernel process work lands underneath.
 */

#include <sys/types.h>
#include <errno.h>
#include <stdint.h>

extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                int64_t a2, int64_t a3, int64_t a4);

#define SYS_FORK 57
#define SYS_EXEC 59
#define SYS_WAIT 61

extern char **environ;

pid_t fork(void) {
    long ret = (long)simpleos_syscall(SYS_FORK, 0, 0, 0, 0, 0);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    return (pid_t)ret;
}

int execve(const char *path, char *const argv[], char *const envp[]) {
    long ret = (long)simpleos_syscall(SYS_EXEC,
        (long)(uintptr_t)path,
        (long)(uintptr_t)argv,
        (long)(uintptr_t)envp, 0, 0);
    if (ret < 0) errno = (int)(-ret);
    return -1;
}

int execv(const char *path, char *const argv[]) {
    return execve(path, argv, environ);
}

int execvp(const char *file, char *const argv[]) {
    return execv(file, argv);
}

pid_t simpleos_waitpid(pid_t pid, int *wstatus, int options) {
    int status_buf = 0;
    long ret = (long)simpleos_syscall(SYS_WAIT, (long)pid,
                                      (long)(uintptr_t)&status_buf,
                                      (long)options, 0, 0);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    if (wstatus) *wstatus = status_buf;
    return (pid_t)ret;
}
