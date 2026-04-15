/*
 * SimpleOS Libc Shim — Process stubs, environment, sleep, sysconf
 *
 * Process creation (fork/exec) returns ENOSYS — SimpleOS is single-process.
 * Environment variables are stored in a static table (256 entries max).
 * Sleep delegates to syscall 51 (nanosleep).
 */

#include "include/unistd.h"
#include "include/stdlib.h"
#include "include/errno.h"
#include "include/string.h"
#include "include/sys/types.h"

extern int64_t simpleos_syscall(int64_t, int64_t, int64_t, int64_t,
                                 int64_t, int64_t);
extern int errno;

/* ====================================================================
 * 1. Environment variable table
 * ==================================================================== */

static char *_env_storage[256];
static int _env_count = 0;
char **environ = _env_storage;

char *getenv(const char *name) {
    size_t len = strlen(name);
    for (int i = 0; i < _env_count; i++) {
        if (_env_storage[i] &&
            strncmp(_env_storage[i], name, len) == 0 &&
            _env_storage[i][len] == '=')
            return _env_storage[i] + len + 1;
    }
    return NULL;
}

int setenv(const char *name, const char *value, int overwrite) {
    size_t nlen = strlen(name);
    size_t vlen = strlen(value);

    /* Check if already exists */
    for (int i = 0; i < _env_count; i++) {
        if (_env_storage[i] &&
            strncmp(_env_storage[i], name, nlen) == 0 &&
            _env_storage[i][nlen] == '=') {
            if (!overwrite) return 0;
            char *entry = (char *)malloc(nlen + vlen + 2);
            if (!entry) { errno = ENOMEM; return -1; }
            memcpy(entry, name, nlen);
            entry[nlen] = '=';
            memcpy(entry + nlen + 1, value, vlen + 1);
            _env_storage[i] = entry;
            return 0;
        }
    }

    if (_env_count >= 255) { errno = ENOMEM; return -1; }

    char *entry = (char *)malloc(nlen + vlen + 2);
    if (!entry) { errno = ENOMEM; return -1; }
    memcpy(entry, name, nlen);
    entry[nlen] = '=';
    memcpy(entry + nlen + 1, value, vlen + 1);
    _env_storage[_env_count++] = entry;
    _env_storage[_env_count] = NULL;
    return 0;
}

int unsetenv(const char *name) {
    size_t len = strlen(name);
    for (int i = 0; i < _env_count; i++) {
        if (_env_storage[i] &&
            strncmp(_env_storage[i], name, len) == 0 &&
            _env_storage[i][len] == '=') {
            for (int j = i; j < _env_count - 1; j++)
                _env_storage[j] = _env_storage[j + 1];
            _env_count--;
            _env_storage[_env_count] = NULL;
            return 0;
        }
    }
    return 0;
}

/* ====================================================================
 * 2. Process control stubs
 * ==================================================================== */

pid_t fork(void) {
    errno = ENOSYS;
    return -1;
}

int execve(const char *path, char *const argv[], char *const envp[]) {
    (void)path; (void)argv; (void)envp;
    errno = ENOSYS;
    return -1;
}

int execvp(const char *file, char *const argv[]) {
    (void)file; (void)argv;
    errno = ENOSYS;
    return -1;
}

pid_t getppid(void) {
    return (pid_t)simpleos_syscall(4, 1, 0, 0, 0, 0);
}

uid_t getuid(void)  { return 0; }
gid_t getgid(void)  { return 0; }
uid_t geteuid(void) { return 0; }
gid_t getegid(void) { return 0; }

int system(const char *cmd) {
    (void)cmd;
    errno = ENOSYS;
    return -1;
}

/* ====================================================================
 * 3. Sleep
 * ==================================================================== */

unsigned int sleep(unsigned int seconds) {
    simpleos_syscall(51, (int64_t)seconds * 1000000000LL, 0, 0, 0, 0);
    return 0;
}

int usleep(useconds_t usec) {
    simpleos_syscall(51, (int64_t)usec * 1000LL, 0, 0, 0, 0);
    return 0;
}

/* ====================================================================
 * 4. System configuration
 * ==================================================================== */

long sysconf(int name) {
    switch (name) {
    case _SC_PAGESIZE:         return 4096;
    case _SC_NPROCESSORS_CONF: return 1;
    case 84:                   return 1;   /* _SC_NPROCESSORS_ONLN */
    default:
        errno = EINVAL;
        return -1;
    }
}
