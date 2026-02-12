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
 * Offset-based File I/O
 * ---------------------------------------------------------------- */

const char* rt_file_read_text_at(const char* path, int64_t offset, int64_t size) {
    if (!path || size <= 0 || offset < 0) return "";

    HANDLE hFile = CreateFileA(path, GENERIC_READ, FILE_SHARE_READ, NULL,
                               OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (hFile == INVALID_HANDLE_VALUE) return "";

    /* Allocate buffer with null terminator */
    char* buffer = (char*)malloc((size_t)size + 1);
    if (!buffer) {
        CloseHandle(hFile);
        return "";
    }

    /* Set file pointer */
    LARGE_INTEGER li_offset;
    li_offset.QuadPart = offset;
    if (!SetFilePointerEx(hFile, li_offset, NULL, FILE_BEGIN)) {
        CloseHandle(hFile);
        free(buffer);
        return "";
    }

    /* Read data */
    DWORD bytes_read = 0;
    if (!ReadFile(hFile, buffer, (DWORD)size, &bytes_read, NULL)) {
        CloseHandle(hFile);
        free(buffer);
        return "";
    }

    CloseHandle(hFile);
    buffer[bytes_read] = '\0';
    return buffer;
}

int64_t rt_file_write_text_at(const char* path, int64_t offset, const char* data) {
    if (!path || !data || offset < 0) return -1;

    int64_t size = (int64_t)strlen(data);
    if (size == 0) return 0;

    /* Open or create file, preserve existing content */
    HANDLE hFile = CreateFileA(path, GENERIC_WRITE, 0, NULL,
                               OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    if (hFile == INVALID_HANDLE_VALUE) return -1;

    /* Set file pointer */
    LARGE_INTEGER li_offset;
    li_offset.QuadPart = offset;
    if (!SetFilePointerEx(hFile, li_offset, NULL, FILE_BEGIN)) {
        CloseHandle(hFile);
        return -1;
    }

    /* Write data */
    DWORD bytes_written = 0;
    if (!WriteFile(hFile, data, (DWORD)size, &bytes_written, NULL)) {
        CloseHandle(hFile);
        return -1;
    }

    CloseHandle(hFile);
    return (int64_t)bytes_written;
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

/* ----------------------------------------------------------------
 * Process Async
 * ---------------------------------------------------------------- */

int64_t rt_process_spawn_async(const char* cmd, const char** args, int64_t arg_count) {
    if (!cmd) return -1;

    /* Build command line */
    char cmdline[4096] = {0};
    snprintf(cmdline, sizeof(cmdline), "%s", cmd);
    for (int64_t i = 0; i < arg_count; i++) {
        strncat(cmdline, " ", sizeof(cmdline) - strlen(cmdline) - 1);
        strncat(cmdline, args[i], sizeof(cmdline) - strlen(cmdline) - 1);
    }

    STARTUPINFOA si = {0};
    PROCESS_INFORMATION pi = {0};
    si.cb = sizeof(si);

    if (!CreateProcessA(NULL, cmdline, NULL, NULL, FALSE, 0, NULL, NULL, &si, &pi)) {
        return -1;
    }

    CloseHandle(pi.hThread);
    int64_t pid = (int64_t)pi.hProcess;
    return pid;
}

int64_t rt_process_wait(int64_t pid, int64_t timeout_ms) {
    if (pid <= 0) return -1;

    HANDLE hProcess = (HANDLE)pid;
    DWORD timeout = (timeout_ms <= 0) ? INFINITE : (DWORD)timeout_ms;

    DWORD result = WaitForSingleObject(hProcess, timeout);
    if (result == WAIT_TIMEOUT) {
        return -2;  /* Timeout */
    }
    if (result != WAIT_OBJECT_0) {
        return -1;  /* Error */
    }

    DWORD exit_code = 0;
    if (!GetExitCodeProcess(hProcess, &exit_code)) {
        return -1;
    }

    CloseHandle(hProcess);
    return (int64_t)exit_code;
}

bool rt_process_is_running(int64_t pid) {
    if (pid <= 0) return false;

    HANDLE hProcess = (HANDLE)pid;
    DWORD exit_code = 0;

    if (!GetExitCodeProcess(hProcess, &exit_code)) {
        return false;
    }

    return exit_code == STILL_ACTIVE;
}

bool rt_process_kill(int64_t pid) {
    if (pid <= 0) return false;

    HANDLE hProcess = (HANDLE)pid;
    if (!TerminateProcess(hProcess, 1)) {
        return false;
    }

    CloseHandle(hProcess);
    return true;
}

#endif /* SPL_PLATFORM_WIN_H */
