/*
 * SimpleOS fork/exec/waitpid — IF-01 syscall trampoline.
 *
 * Stub fallback: when SIMPLEOS_HAS_SYSCALL_TRAMPOLINE is undefined (host
 * builds), all functions return -ENOSYS via the inline trampoline.
 * When defined (SimpleOS native), they call the real spl_handle_*
 * kernel handlers wired by WS-K-2.
 */

#include <sys/types.h>
#include <errno.h>
#include <stdint.h>

#ifdef SIMPLEOS_HAS_SYSCALL_TRAMPOLINE
extern long _simpleos_syscall0(long num);
extern long _simpleos_syscall3(long num, long, long, long);
#else
static inline long _simpleos_syscall0(long n) { (void)n; return -38; }
static inline long _simpleos_syscall3(long n, long a, long b, long c) { (void)n;(void)a;(void)b;(void)c; return -38; }
#endif

#define SYS_FORK 50
#define SYS_EXEC 51
#define SYS_WAIT 52

extern char **environ;

pid_t fork(void) {
    long ret = _simpleos_syscall0(SYS_FORK);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    return (pid_t)ret;
}

int execve(const char *path, char *const argv[], char *const envp[]) {
    long ret = _simpleos_syscall3(SYS_EXEC,
        (long)(uintptr_t)path,
        (long)(uintptr_t)argv,
        (long)(uintptr_t)envp);
    errno = (int)(-ret);
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
    long ret = _simpleos_syscall3(SYS_WAIT, (long)pid,
                                  (long)(uintptr_t)&status_buf,
                                  (long)options);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    if (wstatus) *wstatus = status_buf;
    return (pid_t)ret;
}
