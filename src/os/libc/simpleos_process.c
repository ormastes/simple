/*
 * SimpleOS Libc Shim — Environment, identity, sleep, sysconf
 *
 * Process creation lives in simpleos_fork.c so C apps link one canonical
 * fork/exec/wait implementation instead of shadowing it with stubs here.
 * Environment variables are stored in a static table (256 entries max).
 * Sleep delegates to syscall 51 (nanosleep).
 */

#include "include/unistd.h"
#include "include/stdlib.h"
#include "include/errno.h"
#include "include/string.h"
#include "include/sys/types.h"
#include <stdint.h>

extern int64_t simpleos_syscall(int64_t, int64_t, int64_t, int64_t,
                                 int64_t, int64_t);
extern int errno;

/* ====================================================================
 * 1. Environment variable table
 * ==================================================================== */

static char *_env_storage[256];
static int _env_count = 0;
char **environ = _env_storage;

static int _env_name_valid(const char *name) {
    if (!name || name[0] == '\0') return 0;
    size_t i = 0;
    while (name[i] != '\0') {
        if (name[i] == '=') return 0;
        i++;
    }
    return 1;
}

static int _env_entry_size(size_t name_len, size_t value_len, size_t *out_size) {
    /* name + '=' + value + trailing NUL, with no wrapping allocation. */
    if (name_len > (size_t)-1 - 2) return 0;
    if (value_len > (size_t)-1 - name_len - 2) return 0;
    *out_size = name_len + value_len + 2;
    return 1;
}

char *getenv(const char *name) {
    if (!name) {
        errno = EINVAL;
        return NULL;
    }
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
    if (!_env_name_valid(name) || !value) { errno = EINVAL; return -1; }
    size_t nlen = strlen(name);
    size_t vlen = strlen(value);
    size_t entry_size = 0;
    if (!_env_entry_size(nlen, vlen, &entry_size)) { errno = ENOMEM; return -1; }

    char *entry = (char *)malloc(entry_size);
    if (!entry) { errno = ENOMEM; return -1; }
    memcpy(entry, name, nlen);
    entry[nlen] = '=';
    memcpy(entry + nlen + 1, value, vlen + 1);

    /* Check if already exists */
    for (int i = 0; i < _env_count; i++) {
        if (_env_storage[i] &&
            strncmp(_env_storage[i], name, nlen) == 0 &&
            _env_storage[i][nlen] == '=') {
            if (!overwrite) { free(entry); return 0; }
            char *previous = _env_storage[i];
            _env_storage[i] = entry;
            free(previous);
            return 0;
        }
    }

    if (_env_count >= 255) { free(entry); errno = ENOMEM; return -1; }
    _env_storage[_env_count++] = entry;
    _env_storage[_env_count] = NULL;
    return 0;
}

int unsetenv(const char *name) {
    if (!_env_name_valid(name)) { errno = EINVAL; return -1; }
    size_t len = strlen(name);
    for (int i = 0; i < _env_count; i++) {
        if (_env_storage[i] &&
            strncmp(_env_storage[i], name, len) == 0 &&
            _env_storage[i][len] == '=') {
            char *previous = _env_storage[i];
            for (int j = i; j < _env_count - 1; j++)
                _env_storage[j] = _env_storage[j + 1];
            _env_count--;
            _env_storage[_env_count] = NULL;
            free(previous);
            return 0;
        }
    }
    return 0;
}

/* ====================================================================
 * 2. Process identity
 * ==================================================================== */

pid_t getppid(void) {
    return (pid_t)simpleos_syscall(4, 1, 0, 0, 0, 0);
}

uid_t getuid(void)  { return 0; }
gid_t getgid(void)  { return 0; }
uid_t geteuid(void) { return 0; }
gid_t getegid(void) { return 0; }

pid_t setsid(void) {
    return getpid();
}

pid_t getsid(pid_t pid) {
    (void)pid;
    errno = ESRCH;
    return -1;
}

/* SimpleOS has no process-group state at all (note setsid() above just returns
 * the caller's pid, and getsid() reports ESRCH). So the ONLY setpgid() request
 * that is truthfully satisfiable is the one that asks a process to become the
 * leader of its own group -- which is already the standing arrangement here.
 * That case returns 0 because it is genuinely true, not as a courtesy.
 *
 * Every other request would move a process between groups that do not exist.
 * Returning 0 for those would be a fake success of exactly the kind that made
 * the path-based filesystem syscalls untrustworthy (success written over
 * uninitialized state), so they fail closed with EPERM -- the errno POSIX
 * already defines for "cannot place that process in that group". */
int setpgid(pid_t pid, pid_t pgid) {
    pid_t self = getpid();
    pid_t target = (pid == 0) ? self : pid;
    pid_t group = (pgid == 0) ? target : pgid;
    if (target == self && group == self) {
        return 0;
    }
    errno = EPERM;
    return -1;
}

int gethostname(char *name, size_t len) {
    const char host[] = "simpleos";
    if (!name || len == 0) {
        errno = EINVAL;
        return -1;
    }
    strncpy(name, host, len);
    name[len - 1] = '\0';
    return 0;
}

/* getgid/geteuid/getegid used to be defined a SECOND time here, returning
 * ENOSYS/-1, duplicating the single-user `return 0` definitions at the top of
 * this file (with getuid, getppid and friends). clang rejects the file outright:
 *
 *   error: redefinition of 'getgid'  (and 'geteuid', 'getegid')
 *   note: previous definition is here   simpleos_process.c:122
 *
 * so THIS FILE HAS NEVER COMPILED — the same defect class as the
 * runtime_native.c incident recorded in .claude/rules/vcs.md, where source that
 * is well-formed as bytes and passes every tree-structure guard is nonsense to
 * a compiler. It blocks scripts/os/simpleos-sysroot-riscv64.shs, and therefore
 * every SimpleOS user payload (including the in-guest Simple interpreter) on
 * every architecture.
 *
 * The duplicates are deleted rather than the originals, on two grounds:
 *   * SimpleOS is single-user. `getuid` — which had no duplicate and so is not
 *     in question — already returns 0, and a set where getuid succeeds as root
 *     while getgid/geteuid/getegid fail with ENOSYS is incoherent; callers that
 *     check `geteuid() == 0` for a privilege test would read -1 as "not root"
 *     while getuid() said otherwise.
 *   * The surviving block sits with getpid/getppid/setsid/getsid, the section
 *     that is actually maintained against the syscall layer.
 */

/* ====================================================================
 * 3. Sleep
 * ==================================================================== */

unsigned int sleep(unsigned int seconds) {
    const int64_t nanos_per_second = 1000000000LL;
    if ((uint64_t)seconds > (uint64_t)(INT64_MAX / nanos_per_second)) {
        errno = ERANGE;
        return seconds;
    }
    int64_t result = simpleos_syscall(51, (int64_t)seconds * nanos_per_second, 0, 0, 0, 0);
    if (result < 0) {
        errno = (int)(-result);
        /* No kernel partial-duration receipt exists; returning the full
         * request is the conservative POSIX remaining-time result. */
        return seconds;
    }
    return 0;
}

int usleep(useconds_t usec) {
    int64_t result = simpleos_syscall(51, (int64_t)usec * 1000LL, 0, 0, 0, 0);
    if (result < 0) {
        errno = (int)(-result);
        return -1;
    }
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
