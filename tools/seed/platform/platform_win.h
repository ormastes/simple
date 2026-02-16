/*
 * Windows platform header — headers, compatibility macros, and stubs.
 *
 * Supports two Windows build modes:
 * 1. ClangCL (MSVC ABI): clang-cl with UCRT, MSVC-compatible
 * 2. MinGW Clang (GCC ABI): clang with MinGW target, GCC-compatible
 */
#ifndef SPL_PLATFORM_WIN_H
#define SPL_PLATFORM_WIN_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Windows API headers */
#if defined(_MSC_VER) || defined(SPL_TOOLCHAIN_CLANGCL)
    /* ClangCL or MSVC: Use Windows SDK headers */
    #include <io.h>
    #include <process.h>
    #include <windows.h>

    /* MSVC-specific compatibility */
    #define popen  _popen
    #define pclose _pclose
    #define strdup _strdup
#else
    /* MinGW Clang: Use mingw-w64 headers */
    #include <windows.h>
    #include <io.h>
    #include <process.h>

    /* MinGW provides POSIX-compatible names directly */
    /* No need to redefine strdup, popen, pclose */
#endif

/* ----------------------------------------------------------------
 * Directory Operations (stub)
 * ---------------------------------------------------------------- */

bool rt_dir_create(const char* path, bool recursive) {
    (void)recursive;
    if (!path) return false;
    return CreateDirectoryA(path, NULL) || GetLastError() == ERROR_ALREADY_EXISTS;
}

const char** rt_dir_list(const char* path, int64_t* out_count) {
    if (!path || !out_count) {
        if (out_count) *out_count = 0;
        return NULL;
    }

    /* Build search pattern: path + "\\*" */
    size_t path_len = strlen(path);
    char* search_pattern = malloc(path_len + 3);
    if (!search_pattern) {
        *out_count = 0;
        return NULL;
    }
    strcpy(search_pattern, path);
    if (path_len > 0 && path[path_len - 1] != '\\' && path[path_len - 1] != '/') {
        strcat(search_pattern, "\\");
    }
    strcat(search_pattern, "*");

    /* First pass: count entries (excluding . and ..) */
    WIN32_FIND_DATAA find_data;
    HANDLE hFind = FindFirstFileA(search_pattern, &find_data);
    if (hFind == INVALID_HANDLE_VALUE) {
        free(search_pattern);
        *out_count = 0;
        return NULL;
    }

    int64_t count = 0;
    do {
        if (strcmp(find_data.cFileName, ".") != 0 && strcmp(find_data.cFileName, "..") != 0) {
            count++;
        }
    } while (FindNextFileA(hFind, &find_data));
    FindClose(hFind);

    if (count == 0) {
        free(search_pattern);
        *out_count = 0;
        return NULL;
    }

    /* Second pass: collect entries */
    const char** result = malloc(sizeof(char*) * (count + 1));
    if (!result) {
        free(search_pattern);
        *out_count = 0;
        return NULL;
    }

    hFind = FindFirstFileA(search_pattern, &find_data);
    free(search_pattern);

    if (hFind == INVALID_HANDLE_VALUE) {
        free(result);
        *out_count = 0;
        return NULL;
    }

    int64_t i = 0;
    do {
        if (strcmp(find_data.cFileName, ".") != 0 && strcmp(find_data.cFileName, "..") != 0 && i < count) {
            result[i++] = _strdup(find_data.cFileName);
        }
    } while (FindNextFileA(hFind, &find_data));
    FindClose(hFind);

    result[count] = NULL;
    *out_count = count;
    return result;
}

void rt_dir_list_free(const char** entries, int64_t count) {
    (void)entries; (void)count;
}

/* Helper: Recursively remove directory contents */
static bool rt_dir_remove_all_impl(const char* path) {
    if (!path) return false;

    /* Build search pattern */
    size_t path_len = strlen(path);
    char* search_pattern = malloc(path_len + 3);
    if (!search_pattern) return false;
    strcpy(search_pattern, path);
    if (path_len > 0 && path[path_len - 1] != '\\' && path[path_len - 1] != '/') {
        strcat(search_pattern, "\\");
    }
    strcat(search_pattern, "*");

    WIN32_FIND_DATAA find_data;
    HANDLE hFind = FindFirstFileA(search_pattern, &find_data);
    free(search_pattern);

    if (hFind == INVALID_HANDLE_VALUE) {
        return RemoveDirectoryA(path);
    }

    bool success = true;
    do {
        if (strcmp(find_data.cFileName, ".") == 0 || strcmp(find_data.cFileName, "..") == 0) {
            continue;
        }

        /* Build full path: path + "\\" + filename */
        size_t full_len = path_len + 1 + strlen(find_data.cFileName) + 1;
        char* full_path = malloc(full_len);
        if (!full_path) {
            success = false;
            continue;
        }
        strcpy(full_path, path);
        if (path_len > 0 && path[path_len - 1] != '\\' && path[path_len - 1] != '/') {
            strcat(full_path, "\\");
        }
        strcat(full_path, find_data.cFileName);

        if (find_data.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) {
            /* Recursively remove subdirectory */
            if (!rt_dir_remove_all_impl(full_path)) {
                success = false;
            }
        } else {
            /* Delete file */
            if (!DeleteFileA(full_path)) {
                success = false;
            }
        }
        free(full_path);
    } while (FindNextFileA(hFind, &find_data));

    FindClose(hFind);

    /* Remove the directory itself */
    if (!RemoveDirectoryA(path)) {
        success = false;
    }

    return success;
}

bool rt_dir_remove_all(const char* path) {
    return rt_dir_remove_all_impl(path);
}

/* ----------------------------------------------------------------
 * File Locking (stub)
 * ---------------------------------------------------------------- */

int64_t rt_file_lock(const char* path, int64_t timeout_secs) {
    if (!path) return -1;

    /* Open or create file for locking */
    HANDLE hFile = CreateFileA(
        path,
        GENERIC_READ | GENERIC_WRITE,
        FILE_SHARE_READ | FILE_SHARE_WRITE,
        NULL,
        OPEN_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );

    if (hFile == INVALID_HANDLE_VALUE) {
        return -1;
    }

    /* Set up lock parameters */
    OVERLAPPED overlapped = {0};
    DWORD flags = LOCKFILE_EXCLUSIVE_LOCK;

    if (timeout_secs <= 0) {
        /* Blocking lock */
        if (!LockFileEx(hFile, flags, 0, MAXDWORD, MAXDWORD, &overlapped)) {
            CloseHandle(hFile);
            return -1;
        }
    } else {
        /* Non-blocking lock with timeout via polling */
        flags |= LOCKFILE_FAIL_IMMEDIATELY;
        int64_t start_time = (int64_t)GetTickCount64();
        int64_t timeout_ms = timeout_secs * 1000;

        while (1) {
            if (LockFileEx(hFile, flags, 0, MAXDWORD, MAXDWORD, &overlapped)) {
                break;  /* Lock acquired */
            }

            /* Check timeout */
            int64_t elapsed = (int64_t)GetTickCount64() - start_time;
            if (elapsed >= timeout_ms) {
                CloseHandle(hFile);
                return -1;  /* Timeout */
            }

            /* Wait a bit before retrying */
            Sleep(50);
        }
    }

    return (int64_t)hFile;
}

bool rt_file_unlock(int64_t handle) {
    if (handle <= 0) return false;

    HANDLE hFile = (HANDLE)handle;
    OVERLAPPED overlapped = {0};

    UnlockFileEx(hFile, 0, MAXDWORD, MAXDWORD, &overlapped);
    CloseHandle(hFile);

    return true;
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
 * Memory-Mapped File I/O
 * ---------------------------------------------------------------- */

void* rt_mmap(const char* path, int64_t size, int64_t offset, bool readonly) {
    if (!path || size <= 0 || offset < 0) return NULL;

    DWORD access = readonly ? GENERIC_READ : (GENERIC_READ | GENERIC_WRITE);
    DWORD share = FILE_SHARE_READ;
    DWORD protect = readonly ? PAGE_READONLY : PAGE_READWRITE;
    DWORD map_access = readonly ? FILE_MAP_READ : FILE_MAP_WRITE;

    HANDLE hFile = CreateFileA(path, access, share, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (hFile == INVALID_HANDLE_VALUE) return NULL;

    HANDLE hMapping = CreateFileMappingA(hFile, NULL, protect, 0, 0, NULL);
    if (!hMapping) {
        CloseHandle(hFile);
        return NULL;
    }

    DWORD offset_high = (DWORD)(offset >> 32);
    DWORD offset_low = (DWORD)(offset & 0xFFFFFFFF);

    void* addr = MapViewOfFile(hMapping, map_access, offset_high, offset_low, (SIZE_T)size);

    CloseHandle(hMapping);
    CloseHandle(hFile);

    return addr;
}

bool rt_munmap(void* addr, int64_t size) {
    (void)size;  /* Not needed on Windows */
    if (!addr) return false;
    return UnmapViewOfFile(addr) != 0;
}

bool rt_madvise(void* addr, int64_t size, int64_t advice) {
    if (!addr || size <= 0) return false;

    /* Windows doesn't have direct equivalent - use PrefetchVirtualMemory for WILLNEED */
    if (advice == 3) {  /* WILLNEED */
        /* PrefetchVirtualMemory only available in Win8+ */
        return true;  /* Silently succeed - not critical */
    }
    return true;  /* Other advice types not supported, but not an error */
}

bool rt_msync(void* addr, int64_t size) {
    if (!addr || size <= 0) return false;
    return FlushViewOfFile(addr, (SIZE_T)size) != 0;
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
