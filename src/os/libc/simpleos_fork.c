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
#include <string.h>

extern int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1,
                                int64_t a2, int64_t a3, int64_t a4);

#define SYS_FORK 57
#define SYS_EXEC 59
#define SYS_WAIT 61

extern char **environ;

static int running_on_linux_host(void) {
#if defined(__x86_64__)
    uint64_t cs;
    __asm__ volatile ("mov %%cs, %0" : "=r"(cs));
    return cs == 0x33;
#else
    return 0;
#endif
}

static int64_t linux_syscall0(int64_t id) {
#if defined(__x86_64__)
    int64_t r;
    __asm__ volatile("syscall"
                     : "=a"(r)
                     : "a"(id)
                     : "rcx", "r11", "memory");
    return r;
#else
    (void)id;
    return -38;
#endif
}

static int64_t linux_syscall3(int64_t id, int64_t a0, int64_t a1, int64_t a2) {
#if defined(__x86_64__)
    int64_t r;
    __asm__ volatile("syscall"
                     : "=a"(r)
                     : "a"(id), "D"(a0), "S"(a1), "d"(a2)
                     : "rcx", "r11", "memory");
    return r;
#else
    (void)id;
    (void)a0;
    (void)a1;
    (void)a2;
    return -38;
#endif
}

static int64_t linux_syscall4(int64_t id, int64_t a0, int64_t a1, int64_t a2,
                              int64_t a3) {
#if defined(__x86_64__)
    register int64_t r10 __asm__("r10") = a3;
    int64_t r;
    __asm__ volatile("syscall"
                     : "=a"(r)
                     : "a"(id), "D"(a0), "S"(a1), "d"(a2), "r"(r10)
                     : "rcx", "r11", "memory");
    return r;
#else
    (void)id;
    (void)a0;
    (void)a1;
    (void)a2;
    (void)a3;
    return -38;
#endif
}

pid_t fork(void) {
    if (running_on_linux_host()) {
        long ret = (long)linux_syscall0(57);
        if (ret < 0) { errno = (int)(-ret); return -1; }
        return (pid_t)ret;
    }
    long ret = (long)simpleos_syscall(SYS_FORK, 0, 0, 0, 0, 0);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    return (pid_t)ret;
}

int execve(const char *path, char *const argv[], char *const envp[]) {
    if (!path) {
        errno = EFAULT;
        return -1;
    }
    if (running_on_linux_host()) {
        long ret = (long)linux_syscall3(59, (long)(uintptr_t)path,
                                        (long)(uintptr_t)argv,
                                        (long)(uintptr_t)envp);
        if (ret < 0) errno = (int)(-ret);
        else errno = EIO;
        return -1;
    }
    long ret = (long)simpleos_syscall(SYS_EXEC,
        (long)(uintptr_t)path,
        (long)strlen(path),
        (long)(uintptr_t)argv,
        (long)(uintptr_t)envp, 0);
    if (ret < 0) errno = (int)(-ret);
    else errno = EIO;
    return -1;
}

int execv(const char *path, char *const argv[]) {
    return execve(path, argv, environ);
}

int execvp(const char *file, char *const argv[]) {
    if (!file || file[0] == '\0') {
        errno = ENOENT;
        return -1;
    }
    for (const char *p = file; *p; p++) {
        if (*p == '/') return execv(file, argv);
    }

    /* SimpleOS images install executable tools in these two canonical roots. */
    static const char *const roots[] = { "/usr/bin/", "/bin/" };
    char path[512];
    size_t file_len = strlen(file);
    for (size_t i = 0; i < sizeof(roots) / sizeof(roots[0]); i++) {
        size_t root_len = strlen(roots[i]);
        if (root_len + file_len + 1 > sizeof(path)) {
            errno = ENAMETOOLONG;
            continue;
        }
        memcpy(path, roots[i], root_len);
        memcpy(path + root_len, file, file_len + 1);
        execv(path, argv);
    }
    return -1;
}

pid_t simpleos_waitpid(pid_t pid, int *wstatus, int options) {
    if (running_on_linux_host()) {
        long ret = (long)linux_syscall4(61, (long)pid,
                                        (long)(uintptr_t)wstatus,
                                        (long)options, 0);
        if (ret < 0) { errno = (int)(-ret); return -1; }
        return (pid_t)ret;
    }
    int status_buf = 0;
    long ret = (long)simpleos_syscall(SYS_WAIT, (long)pid,
                                      (long)(uintptr_t)&status_buf,
                                      (long)options, 0, 0);
    if (ret < 0) { errno = (int)(-ret); return -1; }
    if (wstatus) *wstatus = status_buf;
    return (pid_t)ret;
}
