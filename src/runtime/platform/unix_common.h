/*
 * Shared POSIX implementation — Linux, macOS, FreeBSD.
 *
 * Included by platform_linux.h / platform_macos.h / platform_freebsd.h /
 * platform_openbsd.h / platform_netbsd.h
 * AFTER they define any platform-specific feature-test macros.
 */
#ifndef SPL_UNIX_COMMON_H
#define SPL_UNIX_COMMON_H

#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif
#ifndef _XOPEN_SOURCE
#define _XOPEN_SOURCE 700
#endif
#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE
#endif
#ifndef _BSD_SOURCE
#define _BSD_SOURCE
#endif

/* POSIX headers */
#include <ftw.h>
#include <sys/file.h>
#include <fcntl.h>
#include <unistd.h>
#include <dlfcn.h>
#include <sys/mman.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <signal.h>
#include <dirent.h>
#include <errno.h>
#include <limits.h>

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>

/* ----------------------------------------------------------------
 * Directory Operations
 * ---------------------------------------------------------------- */

static int unlink_cb(const char *fpath, const struct stat *sb,
                     int typeflag, struct FTW *ftwbuf) {
    (void)sb; (void)typeflag; (void)ftwbuf;
    return remove(fpath);
}

/* C-string worker. The public rt_dir_* entry point lives in runtime.c and
 * converts the compiler's (ptr, len) `text` pair before calling this; a Simple
 * `text` is not NUL-terminated. See rt_text_arg_to_path in runtime.c. */
bool rt_dir_create_cpath(const char* path, bool recursive) {
    if (!path) return false;
    
    if (!recursive) {
        return mkdir(path, 0755) == 0 || errno == EEXIST;
    }
    
    /* Recursive mkdir -p logic */
    char tmp[PATH_MAX];
    char* p = NULL;
    size_t len;
    
    len = strlen(path);
    if (len == 0) return false;
    if (len >= sizeof(tmp)) return false;
    
    strncpy(tmp, path, sizeof(tmp) - 1);
    tmp[sizeof(tmp) - 1] = '\0';
    
    /* Remove trailing slash */
    if (tmp[len - 1] == '/') {
        tmp[len - 1] = '\0';
    }
    
    /* Create parent directories */
    for (p = tmp + 1; *p; p++) {
        if (*p == '/') {
            *p = '\0';
            if (mkdir(tmp, 0755) != 0 && errno != EEXIST) {
                return false;
            }
            *p = '/';
        }
    }
    
    /* Create final directory */
    return mkdir(tmp, 0755) == 0 || errno == EEXIST;
}

/* C-string worker. The public rt_dir_list entry point lives in runtime.c and
 * converts the compiler's (ptr, len) `text` pair before calling this.
 *
 * This used to BE `rt_dir_list`, which was catastrophic: runtime_sffi.rs:1888
 * declares rt_dir_list as `(path_ptr, path_len) -> RuntimeValue`, so the
 * compiler passed a LENGTH where this signature reads an `int64_t* out_count`
 * and wrote through it -- an immediate SIGSEGV, reproduced in all three C link
 * orders, for an existing directory AND a missing one. The arities happened to
 * match (2 and 2), which is why the extern ABI gate's arity check never saw it;
 * only the return-class check (const char** vs I64) flagged the row. */
const char** rt_dir_list_cpath(const char* path, int64_t* out_count) {
    if (!path || !out_count) {
        if (out_count) *out_count = 0;
        return NULL;
    }
    
    DIR* dir = opendir(path);
    if (!dir) {
        *out_count = 0;
        return NULL;
    }
    
    /* Count entries (excluding . and ..) */
    int64_t count = 0;
    struct dirent* ent;
    while ((ent = readdir(dir)) != NULL) {
        if (strcmp(ent->d_name, ".") != 0 && strcmp(ent->d_name, "..") != 0) {
            count++;
        }
    }
    
    if (count == 0) {
        closedir(dir);
        *out_count = 0;
        return NULL;
    }
    
    /* Allocate array (null-terminated) */
    const char** result = malloc(sizeof(char*) * (count + 1));
    if (!result) {
        closedir(dir);
        *out_count = 0;
        return NULL;
    }
    
    /* Read entries again */
    rewinddir(dir);
    int64_t i = 0;
    while ((ent = readdir(dir)) != NULL && i < count) {
        if (strcmp(ent->d_name, ".") != 0 && strcmp(ent->d_name, "..") != 0) {
            result[i++] = strdup(ent->d_name);
        }
    }
    result[count] = NULL;
    closedir(dir);
    
    *out_count = count;
    return result;
}

void rt_dir_list_free(const char** entries, int64_t count) {
    if (!entries) return;
    for (int64_t i = 0; i < count; i++) {
        free((void*)entries[i]);
    }
    free((void*)entries);
}

/* C-string worker. The public rt_dir_* entry point lives in runtime.c and
 * converts the compiler's (ptr, len) `text` pair before calling this; a Simple
 * `text` is not NUL-terminated. See rt_text_arg_to_path in runtime.c. */
bool rt_dir_remove_all_cpath(const char* path) {
    if (!path) return false;
    return nftw(path, unlink_cb, 64, FTW_DEPTH | FTW_PHYS) == 0;
}

/* ----------------------------------------------------------------
 * File Locking
 * ---------------------------------------------------------------- */

/* ABI corrected 2026-08-23: a Simple `text` argument is lowered by codegen to
 * TWO arguments (rt_string_data, rt_string_len) -- verified by objdump -dr on
 * the emitted call site. The old `const char* path` / `void* addr` shapes here
 * matched no caller and no declaration, and none of these symbols had a
 * definition in any ARCHIVE-MEMBER translation unit (this header is included
 * only by runtime.c, which is deliberately not an archive member), so every
 * one of them linked as a NULL GOT slot. */
static int rt_unix_text_to_path(const uint8_t* ptr, uint64_t len, char* buf, size_t buf_size) {
    if (!ptr && len != 0) return 0;
    if (len >= (uint64_t)buf_size) return 0;
    if (len != 0) memcpy(buf, ptr, (size_t)len);
    buf[(size_t)len] = '\0';
    return 1;
}

int64_t rt_file_lock(const uint8_t* path_ptr, uint64_t path_len, int64_t timeout_secs) {
    char path[4096];
    if (!rt_unix_text_to_path(path_ptr, path_len, path, sizeof(path))) return -1;

    int fd = open(path, O_RDWR | O_CREAT, 0644);
    if (fd < 0) return -1;

    if (timeout_secs <= 0) {
        int result = flock(fd, LOCK_EX);
        if (result == 0) return fd;
        close(fd);
        return -1;
    }

    int64_t timeout_ms = timeout_secs > (INT64_MAX / 1000) ? INT64_MAX : timeout_secs * 1000;
    const int64_t sleep_ms = 50;
    struct timespec req;
    req.tv_sec = 0;
    req.tv_nsec = sleep_ms * 1000000LL;

    int64_t waited_ms = 0;
    while (waited_ms <= timeout_ms) {
        int result = flock(fd, LOCK_EX | LOCK_NB);
        if (result == 0) return fd;
        if (errno != EWOULDBLOCK && errno != EAGAIN) {
            close(fd);
            return -1;
        }
        if (waited_ms >= timeout_ms) break;
        nanosleep(&req, NULL);
        waited_ms += sleep_ms;
    }

    close(fd);
    return -1;
}

bool rt_file_unlock(int64_t handle) {
    if (handle < 0) return false;
    flock((int)handle, LOCK_UN);
    close((int)handle);
    return true;
}

/* ----------------------------------------------------------------
 * Offset-based File I/O
 * ---------------------------------------------------------------- */

/* SFFI_LEGACY_UNSAFE: mixed static/heap ownership; checked managed-text callers
 * must not bind this compatibility export. */
const char* rt_file_read_text_at(const char* path, int64_t offset, int64_t size) {
    if (!path || size <= 0 || offset < 0) return "";

    int fd = open(path, O_RDONLY);
    if (fd < 0) return "";

    /* Allocate buffer with null terminator */
    char* buffer = (char*)malloc((size_t)size + 1);
    if (!buffer) {
        close(fd);
        return "";
    }

    ssize_t bytes_read = pread(fd, buffer, (size_t)size, (off_t)offset);
    close(fd);

    if (bytes_read < 0) {
        free(buffer);
        return "";
    }

    buffer[bytes_read] = '\0';
    return buffer;
}

static inline const char* rt_file_text_at_string_data(int64_t value, int64_t* len_out) {
    const uint64_t tag_mask = 0x7ULL;
    const uint64_t heap_tag = 0x1ULL;
    uint64_t raw = (uint64_t)value;
    if ((raw & tag_mask) == heap_tag) {
        const uint8_t* data = rt_string_data(value);
        int64_t len = rt_string_len(value);
        if (data) {
            *len_out = len;
            return (const char*)data;
        }
    }
    if (raw > 4096) {
        const char* s = (const char*)(uintptr_t)raw;
        *len_out = (int64_t)strlen(s);
        return s;
    }
    *len_out = 0;
    return NULL;
}

static inline int64_t rt_file_text_at_int(int64_t value) {
    if ((((uint64_t)value) & 0x7ULL) == 0) return value >> 3;
    return value;
}

int64_t rt_file_write_text_at(int64_t path_value, int64_t offset_value, int64_t data_value) {
    int64_t path_len = 0;
    int64_t data_len = 0;
    const char* path = rt_file_text_at_string_data(path_value, &path_len);
    const char* data = rt_file_text_at_string_data(data_value, &data_len);
    int64_t offset = rt_file_text_at_int(offset_value);
    (void)path_len;
    if (!path || !data || offset < 0 || data_len < 0) return -1;

    int64_t size = data_len;
    if (size == 0) return 0;

    /* Open or create file, preserve existing content */
    int fd = open(path, O_WRONLY | O_CREAT, 0644);
    if (fd < 0) return -1;

    ssize_t bytes_written = pwrite(fd, data, (size_t)size, (off_t)offset);
    close(fd);

    return (int64_t)bytes_written;
}

/* ----------------------------------------------------------------
 * Memory-Mapped File I/O
 * ---------------------------------------------------------------- */

int64_t rt_mmap(const uint8_t* path_ptr, uint64_t path_len, int64_t size, int64_t offset, int64_t readonly) {
    char path[4096];
    if (!rt_unix_text_to_path(path_ptr, path_len, path, sizeof(path))) return 0;
    if (size <= 0 || offset < 0) return 0;

    int prot = readonly != 0 ? PROT_READ : (PROT_READ | PROT_WRITE);
    int flags = MAP_SHARED;
    int open_flags = readonly != 0 ? O_RDONLY : O_RDWR;

    int fd = open(path, open_flags);
    if (fd < 0) return 0;

    void* addr = mmap(NULL, (size_t)size, prot, flags, fd, (off_t)offset);
    close(fd);

    if (addr == MAP_FAILED) return 0;
    return (int64_t)(uintptr_t)addr;
}

bool rt_munmap(int64_t addr, int64_t size) {
    if (addr == 0 || size <= 0) return false;
    return munmap((void*)(uintptr_t)addr, (size_t)size) == 0;
}

bool rt_madvise(int64_t addr, int64_t size, int64_t advice) {
    if (addr == 0 || size <= 0) return false;

    /* Convert advice codes: 0=NORMAL, 1=RANDOM, 2=SEQUENTIAL, 3=WILLNEED, 4=DONTNEED */
    int posix_advice;
    switch (advice) {
        case 0: posix_advice = MADV_NORMAL; break;
        case 1: posix_advice = MADV_RANDOM; break;
        case 2: posix_advice = MADV_SEQUENTIAL; break;
        case 3: posix_advice = MADV_WILLNEED; break;
        case 4: posix_advice = MADV_DONTNEED; break;
        default: return false;
    }

    return madvise((void*)(uintptr_t)addr, (size_t)size, posix_advice) == 0;
}

bool rt_msync(int64_t addr, int64_t size) {
    if (!addr || size <= 0) return false;
    return msync((void*)(uintptr_t)addr, (size_t)size, MS_SYNC) == 0;
}

/* ----------------------------------------------------------------
 * Raw mmap/mprotect Syscall Wrappers (address-based, for SMF loader)
 * ---------------------------------------------------------------- */

int64_t rt_mmap_raw(int64_t addr, int64_t length, int64_t prot, int64_t flags, int64_t fd, int64_t offset) {
    void* result = mmap((void*)(uintptr_t)addr, (size_t)length, (int)prot, (int)flags, (int)fd, (off_t)offset);
    if (result == MAP_FAILED) return -1;
    return (int64_t)(uintptr_t)result;
}

int64_t rt_munmap_raw(int64_t addr, int64_t length) {
    return (int64_t)munmap((void*)(uintptr_t)addr, (size_t)length);
}

int64_t rt_mprotect(int64_t addr, int64_t length, int64_t prot) {
    return (int64_t)mprotect((void*)(uintptr_t)addr, (size_t)length, (int)prot);
}

int64_t rt_madvise_raw(int64_t addr, int64_t length, int64_t advice) {
    return (int64_t)madvise((void*)(uintptr_t)addr, (size_t)length, (int)advice);
}

int64_t rt_msync_flags(int64_t addr, int64_t length, int64_t flags) {
    return (int64_t)msync((void*)(uintptr_t)addr, (size_t)length, (int)flags);
}

int64_t rt_mlock(int64_t addr, int64_t length) {
    return (int64_t)mlock((void*)(uintptr_t)addr, (size_t)length);
}

int64_t rt_munlock(int64_t addr, int64_t length) {
    return (int64_t)munlock((void*)(uintptr_t)addr, (size_t)length);
}

int64_t rt_open_fd(const char* path, int64_t flags, int64_t mode) {
    return (int64_t)open(path, (int)flags, (mode_t)mode);
}

int64_t rt_close_fd(int64_t fd) {
    return (int64_t)close((int)fd);
}

int64_t rt_page_size(void) {
    return (int64_t)sysconf(_SC_PAGESIZE);
}

/* ----------------------------------------------------------------
 * High-Resolution Time
 * ---------------------------------------------------------------- */

static bool rt_monotonic_time(struct timespec* ts) {
    if (!ts) return false;
#if defined(CLOCK_MONOTONIC_RAW)
    return clock_gettime(CLOCK_MONOTONIC_RAW, ts) == 0;
#elif defined(CLOCK_MONOTONIC)
    return clock_gettime(CLOCK_MONOTONIC, ts) == 0;
#else
    return clock_gettime(CLOCK_REALTIME, ts) == 0;
#endif
}

int64_t rt_time_now_nanos(void) {
    struct timespec ts;
    if (!rt_monotonic_time(&ts)) {
        return -1;
    }
    if (ts.tv_sec < 0 || (int64_t)ts.tv_sec > INT64_MAX / 1000000000LL) return -1;
    if ((int64_t)ts.tv_sec == INT64_MAX / 1000000000LL &&
        ts.tv_nsec > INT64_MAX % 1000000000LL) return -1;
    return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}

int64_t rt_time_now_micros(void) {
    struct timespec ts;
    if (!rt_monotonic_time(&ts)) {
        return -1;
    }
    if (ts.tv_sec < 0 || (int64_t)ts.tv_sec > INT64_MAX / 1000000LL) return -1;
    if ((int64_t)ts.tv_sec == INT64_MAX / 1000000LL &&
        ts.tv_nsec / 1000 > INT64_MAX % 1000000LL) return -1;
    return (int64_t)ts.tv_sec * 1000000LL + (int64_t)ts.tv_nsec / 1000LL;
}

/* ----------------------------------------------------------------
 * Environment
 * ---------------------------------------------------------------- */

void spl_env_set(const char* key, const char* value) {
    if (!key) return;
    if (value) {
        setenv(key, value, 1);
    } else {
        unsetenv(key);
    }
}

/* ----------------------------------------------------------------
 * New Cross-Platform Functions
 * ---------------------------------------------------------------- */

char* rt_getcwd(void) {
    char buf[PATH_MAX];
    if (getcwd(buf, sizeof(buf))) {
        return strdup(buf);
    }
    return strdup(".");
}

bool rt_is_dir(const char* path) {
    if (!path) return false;
    struct stat st;
    return stat(path, &st) == 0 && S_ISDIR(st.st_mode);
}

bool rt_rename(const char* src, const char* dst) {
    if (!src || !dst) return false;
    return rename(src, dst) == 0;
}

void rt_sleep_ms_native(int64_t ms) {
    if (ms <= 0) return;
    struct timespec req;
    req.tv_sec = ms / 1000;
    req.tv_nsec = (ms % 1000) * 1000000LL;
    nanosleep(&req, NULL);
}

int64_t rt_getpid(void) {
    return (int64_t)getpid();
}

char* rt_hostname(void) {
    char buf[256];
    if (gethostname(buf, sizeof(buf)) == 0) {
        buf[sizeof(buf) - 1] = '\0';
        return strdup(buf);
    }
    return strdup("localhost");
}

int64_t rt_thread_available_parallelism(void) {
    long count = sysconf(_SC_NPROCESSORS_ONLN);
    return count > 0 ? (int64_t)count : 1;
}

int64_t rt_time_now_unix_micros(void) {
    struct timeval tv;
    if (gettimeofday(&tv, NULL) == 0) {
        if (tv.tv_sec < 0 || (int64_t)tv.tv_sec > INT64_MAX / 1000000LL) return -1;
        if ((int64_t)tv.tv_sec == INT64_MAX / 1000000LL &&
            tv.tv_usec > INT64_MAX % 1000000LL) return -1;
        return (int64_t)tv.tv_sec * 1000000LL + (int64_t)tv.tv_usec;
    }
    return -1;
}

/* ----------------------------------------------------------------
 * Process Async
 * ---------------------------------------------------------------- */

int64_t rt_process_spawn_async(const char* cmd, const char** args, int64_t arg_count) {
    if (!cmd) return -1;

    pid_t pid = fork();
    if (pid < 0) {
        return -1;  /* Fork failed */
    }

    if (pid == 0) {
        /* Child process */
        char** argv = (char**)malloc(sizeof(char*) * (arg_count + 2));
        if (!argv) _exit(1);

        argv[0] = (char*)cmd;
        for (int64_t i = 0; i < arg_count; i++) {
            argv[i + 1] = (char*)args[i];
        }
        argv[arg_count + 1] = NULL;

        execvp(cmd, argv);
        /* If execvp returns, it failed */
        _exit(127);
    }

    /* Parent process */
    return (int64_t)pid;
}

static void rt_guarded_stop_group(pid_t worker, bool worker_live) {
    if (worker <= 0) return;
    if (kill(-worker, SIGTERM) != 0 && (!worker_live || kill(worker, SIGTERM) != 0)) return;
    usleep(100000);
    (void)kill(-worker, SIGKILL);
    if (worker_live) (void)kill(worker, SIGKILL);
}

/* Supervise ordinary descendants; a child that deliberately calls setsid()
 * escapes this process-group ownership contract. */
int64_t rt_process_spawn_guarded(const char* cmd, const char** args, int64_t arg_count) {
    if (!cmd) return -1;
    pid_t expected_parent = getpid();
    pid_t guardian = fork();
    if (guardian < 0) return -1;
    if (guardian != 0) return (int64_t)guardian;
    if (getppid() != expected_parent) _exit(143);

    pid_t worker = fork();
    if (worker < 0) _exit(127);
    if (worker == 0) {
        (void)setpgid(0, 0);
        char** argv = (char**)malloc(sizeof(char*) * ((size_t)arg_count + 2));
        if (!argv) _exit(1);
        argv[0] = (char*)cmd;
        for (int64_t i = 0; i < arg_count; i++) argv[i + 1] = (char*)args[i];
        argv[arg_count + 1] = NULL;
        execvp(cmd, argv);
        _exit(127);
    }
    (void)setpgid(worker, worker);

    for (;;) {
        int status = 0;
        pid_t waited = waitpid(worker, &status, WNOHANG);
        if (waited == worker) {
            rt_guarded_stop_group(worker, false);
            if (WIFEXITED(status)) _exit(WEXITSTATUS(status));
            if (WIFSIGNALED(status)) {
                int sig = WTERMSIG(status);
                (void)signal(sig, SIG_DFL);
                (void)kill(getpid(), sig);
            }
            _exit(127);
        }
        if (waited < 0 && errno != EINTR) {
            rt_guarded_stop_group(worker, true);
            _exit(127);
        }
        if (getppid() != expected_parent) {
            rt_guarded_stop_group(worker, true);
            while (waitpid(worker, NULL, 0) < 0 && errno == EINTR) {}
            _exit(143);
        }
        usleep(10000);
    }
}

int64_t rt_process_wait(int64_t pid, int64_t timeout_ms) {
    if (pid <= 0) return -1;

    int status;
    if (timeout_ms <= 0) {
        /* No timeout - blocking wait */
        if (waitpid((pid_t)pid, &status, 0) < 0) {
            return -1;
        }
        return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
    }

    /* With timeout - use WNOHANG and poll */
    int64_t elapsed_ms = 0;
    while (elapsed_ms < timeout_ms) {
        pid_t result = waitpid((pid_t)pid, &status, WNOHANG);
        if (result < 0) {
            return -1;  /* Error */
        }
        if (result > 0) {
            /* Process exited */
            return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
        }
        /* Still running - sleep and retry */
        usleep(10000);  /* 10ms */
        elapsed_ms += 10;
    }

    return -2;  /* Timeout */
}

bool rt_process_is_running(int64_t pid) {
    if (pid <= 0) return false;

    /* Try waitpid(WNOHANG) first: this correctly handles direct children.
     * - Returns 0: child still running.
     * - Returns pid: child has exited (zombie reaped); process is NOT running.
     * - Returns -1/ECHILD: pid is not our child — fall through to kill(pid,0).
     * This fixes the bug where a zombie child (exited but not yet reaped) was
     * reported as running because kill(pid,0) returns 0 for zombies. */
    int status;
    pid_t result = waitpid((pid_t)pid, &status, WNOHANG);
    if (result == (pid_t)pid) {
        /* Child exited; we just reaped it. */
        return false;
    }
    if (result == 0) {
        /* waitpid returned 0: child exists and has NOT exited yet. */
        return true;
    }
    /* result == -1: ECHILD means pid is not our child (async-spawned grandchild,
     * or pid was already reaped). Use kill(pid,0) as fallback:
     * - Returns 0 or -1/EPERM: process exists and is running.
     * - Returns -1/ESRCH: process does not exist. */
    if (kill((pid_t)pid, 0) == 0) {
        return true;
    }
    return (errno == EPERM);
}

bool rt_process_kill(int64_t pid) {
    if (pid <= 0) return false;

    /* Send SIGTERM first */
    if (kill((pid_t)pid, SIGTERM) != 0) {
        return false;
    }

    /* Give it 100ms to terminate gracefully */
    usleep(100000);

    /* If still running, send SIGKILL */
    if (rt_process_is_running(pid)) {
        if (kill((pid_t)pid, SIGKILL) != 0) return false;

        /* Reap the child after the forced kill.  Leaving this wait to callers
         * leaks a zombie because the process has already reached a terminal
         * state by the time this function returns. */
        int status;
        while (waitpid((pid_t)pid, &status, 0) < 0) {
            if (errno == EINTR) continue;
            if (errno == ECHILD) break;
            return false;
        }
    }

    return true;
}

/* ----------------------------------------------------------------
 * QMP Unix-Socket Primitives (persistent connection for QMP protocol)
 * ---------------------------------------------------------------- */

#include <sys/socket.h>
#include <sys/un.h>

/* Connect to a Unix-domain stream socket. Returns fd >= 0 on success, -1 on error. */
int64_t rt_unix_socket_connect(const char* path) {
    if (!path) return -1;

    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd < 0) return -1;

    struct sockaddr_un addr;
    memset(&addr, 0, sizeof(addr));
    addr.sun_family = AF_UNIX;
    strncpy(addr.sun_path, path, sizeof(addr.sun_path) - 1);

    if (connect(fd, (struct sockaddr*)&addr, sizeof(addr)) != 0) {
        close(fd);
        return -1;
    }
    return (int64_t)fd;
}

/* Write data to an open fd. Returns bytes written or -1. */
int64_t rt_fd_write(int64_t fd, const char* data, int64_t len) {
    if (fd < 0 || !data || len <= 0) return -1;
    ssize_t n = write((int)fd, data, (size_t)len);
    return (int64_t)n;
}

/* Read up to max bytes from fd, stopping when stop_byte is seen or max reached.
 * Returns a null-terminated heap string (caller must treat as borrowed — runtime GC owns it).
 * Returns "" on error or EOF with no data. */
const char* rt_fd_read_until(int64_t fd, uint8_t stop_byte, int64_t max) {
    if (fd < 0 || max <= 0) return "";

    char* buf = (char*)malloc((size_t)max + 1);
    if (!buf) return "";

    int64_t total = 0;
    while (total < max) {
        ssize_t n = read((int)fd, buf + total, 1);
        if (n <= 0) break;  /* EOF or error */
        total++;
        if ((uint8_t)buf[total - 1] == stop_byte) break;
    }
    buf[total] = '\0';
    return buf;  /* leaked intentionally — matches runtime text ownership model */
}

/* Close an fd. Returns true on success. */
bool rt_fd_close(int64_t fd) {
    if (fd < 0) return false;
    return close((int)fd) == 0;
}

#endif /* SPL_UNIX_COMMON_H */
