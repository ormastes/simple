/*
 * Shared POSIX implementation — Linux, macOS, FreeBSD.
 *
 * Included by platform_linux.h / platform_macos.h / platform_freebsd.h
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
#include <signal.h>
#include <sys/wait.h>
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

bool rt_dir_create(const char* path, bool recursive) {
    if (!path) return false;
    
    if (!recursive) {
        return mkdir(path, 0755) == 0 || errno == EEXIST;
    }
    
    /* Recursive mkdir -p logic */
    char tmp[PATH_MAX];
    char* p = NULL;
    size_t len;
    
    len = strlen(path);
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

const char** rt_dir_list(const char* path, int64_t* out_count) {
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

bool rt_dir_remove_all(const char* path) {
    if (!path) return false;
    return nftw(path, unlink_cb, 64, FTW_DEPTH | FTW_PHYS) == 0;
}

/* ----------------------------------------------------------------
 * File Locking
 * ---------------------------------------------------------------- */

int64_t rt_file_lock(const char* path, int64_t timeout_secs) {
    if (!path) return -1;

    int fd = open(path, O_RDWR | O_CREAT, 0644);
    if (fd < 0) return -1;

    if (timeout_secs > 0) {
        alarm((unsigned int)timeout_secs);
    }

    int result = flock(fd, LOCK_EX);
    alarm(0);

    if (result == 0) return fd;
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

int64_t rt_file_write_text_at(const char* path, int64_t offset, const char* data) {
    if (!path || !data || offset < 0) return -1;

    int64_t size = (int64_t)strlen(data);
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

void* rt_mmap(const char* path, int64_t size, int64_t offset, bool readonly) {
    if (!path || size <= 0 || offset < 0) return NULL;

    int prot = readonly ? PROT_READ : (PROT_READ | PROT_WRITE);
    int flags = MAP_SHARED;
    int open_flags = readonly ? O_RDONLY : O_RDWR;

    int fd = open(path, open_flags);
    if (fd < 0) return NULL;

    void* addr = mmap(NULL, (size_t)size, prot, flags, fd, (off_t)offset);
    close(fd);

    if (addr == MAP_FAILED) return NULL;
    return addr;
}

bool rt_munmap(void* addr, int64_t size) {
    if (!addr || size <= 0) return false;
    return munmap(addr, (size_t)size) == 0;
}

bool rt_madvise(void* addr, int64_t size, int64_t advice) {
    if (!addr || size <= 0) return false;

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

    return madvise(addr, (size_t)size, posix_advice) == 0;
}

bool rt_msync(void* addr, int64_t size) {
    if (!addr || size <= 0) return false;
    return msync(addr, (size_t)size, MS_SYNC) == 0;
}

/* ----------------------------------------------------------------
 * High-Resolution Time
 * ---------------------------------------------------------------- */

int64_t rt_time_now_nanos(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC_RAW, &ts) != 0) {
        return 0;  /* Fallback on error */
    }
    return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}

int64_t rt_time_now_micros(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC_RAW, &ts) != 0) {
        return 0;  /* Fallback on error */
    }
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
 * Dynamic Loading
 * ---------------------------------------------------------------- */

void* spl_dlopen(const char* path) {
    return dlopen(path, RTLD_NOW);
}

void* spl_dlsym(void* handle, const char* name) {
    return dlsym(handle, name);
}

int64_t spl_dlclose(void* handle) {
    return (int64_t)dlclose(handle);
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

    /* Use kill(pid, 0) to check if process exists */
    return kill((pid_t)pid, 0) == 0;
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
        kill((pid_t)pid, SIGKILL);
    }

    return true;
}

#endif /* SPL_UNIX_COMMON_H */
