/*
 * Windows platform header — headers, compatibility macros, and stubs.
 */
#ifndef SPL_PLATFORM_WIN_H
#define SPL_PLATFORM_WIN_H

#include <io.h>
#include <process.h>
#include <windows.h>
#include <stdbool.h>
#include <stdint.h>

#define popen  _popen
#define pclose _pclose
#define strdup _strdup

/* ----------------------------------------------------------------
 * Directory Operations (stub)
 * ---------------------------------------------------------------- */

bool rt_dir_remove_all(const char* path) {
    (void)path;
    return false;
}

/* ----------------------------------------------------------------
 * File Locking (stub)
 * ---------------------------------------------------------------- */

int64_t rt_file_lock(const char* path, int64_t timeout_secs) {
    (void)path; (void)timeout_secs;
    return -1;
}

bool rt_file_unlock(int64_t handle) {
    (void)handle;
    return false;
}

/* ----------------------------------------------------------------
 * High-Resolution Time
 * ---------------------------------------------------------------- */

int64_t rt_time_now_nanos(void) {
    LARGE_INTEGER freq, count;
    if (!QueryPerformanceFrequency(&freq) || !QueryPerformanceCounter(&count)) {
        return 0;
    }
    /* Convert to nanoseconds: (count * 1e9) / freq */
    return (int64_t)((count.QuadPart * 1000000000LL) / freq.QuadPart);
}

int64_t rt_time_now_micros(void) {
    LARGE_INTEGER freq, count;
    if (!QueryPerformanceFrequency(&freq) || !QueryPerformanceCounter(&count)) {
        return 0;
    }
    /* Convert to microseconds: (count * 1e6) / freq */
    return (int64_t)((count.QuadPart * 1000000LL) / freq.QuadPart);
}

/* ----------------------------------------------------------------
 * Environment
 * ---------------------------------------------------------------- */

void spl_env_set(const char* key, const char* value) {
    if (!key) return;
    _putenv_s(key, value ? value : "");
}

/* ----------------------------------------------------------------
 * Dynamic Loading
 * ---------------------------------------------------------------- */

void* spl_dlopen(const char* path) {
    return (void*)LoadLibraryA(path);
}

void* spl_dlsym(void* handle, const char* name) {
    return (void*)GetProcAddress((HMODULE)handle, name);
}

int64_t spl_dlclose(void* handle) {
    return FreeLibrary((HMODULE)handle) ? 0 : -1;
}

#endif /* SPL_PLATFORM_WIN_H */
