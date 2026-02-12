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

/* POSIX headers */
#include <ftw.h>
#include <sys/file.h>
#include <fcntl.h>
#include <unistd.h>
#include <dlfcn.h>

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

#endif /* SPL_UNIX_COMMON_H */
