/* Narrow hosted providers required by core-c-bootstrap tool closures.
 *
 * Keep these out of runtime_native.c: that translation unit is also used by
 * freestanding lanes.  The core-C capsule opts into this file explicitly.
 */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif

#include "runtime.h"

#include <errno.h>
#include <math.h>
#include <stdint.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#include <windows.h>
#include <sys/stat.h>
#undef max
#else
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <unistd.h>
#endif

static char* core_host_strdup(const char* value) {
    size_t length = strlen(value);
    char* result = (char*)malloc(length + 1);
    if (!result) return NULL;
    memcpy(result, value, length + 1);
    return result;
}

char* rt_hostname(void) {
#if defined(_WIN32)
    char buffer[256];
    DWORD length = (DWORD)sizeof(buffer);
    if (GetComputerNameA(buffer, &length)) {
        char* result = (char*)malloc((size_t)length + 1);
        if (!result) return NULL;
        memcpy(result, buffer, (size_t)length);
        result[length] = '\0';
        return result;
    }
#else
    char buffer[256];
    if (gethostname(buffer, sizeof(buffer)) == 0) {
        buffer[sizeof(buffer) - 1] = '\0';
        return core_host_strdup(buffer);
    }
#endif
    return core_host_strdup("localhost");
}

int64_t rt_unix_socket_connect(const char* path) {
#if defined(_WIN32)
    (void)path;
    return -1;
#else
    if (!path) return -1;
    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    struct sockaddr_un address;
    memset(&address, 0, sizeof(address));
    address.sun_family = AF_UNIX;
    if (strlen(path) >= sizeof(address.sun_path)) {
        close(fd);
        return -1;
    }
    memcpy(address.sun_path, path, strlen(path) + 1);
    if (connect(fd, (struct sockaddr*)&address, sizeof(address)) != 0) {
        close(fd);
        return -1;
    }
    return (int64_t)fd;
#endif
}

int64_t rt_metal_is_available(void) {
    /* The portable core capsule has no Objective-C Metal provider. */
    return 0;
}

bool rt_is_debug_mode_enabled(void) {
    return false;
}

int64_t rt_file_stat(const uint8_t* path, uint64_t path_len) {
    if (!path || path_len == 0 || path_len >= 4096) return 0;
    char buffer[4096];
    memcpy(buffer, path, (size_t)path_len);
    buffer[path_len] = '\0';
    struct stat metadata;
    return stat(buffer, &metadata) == 0 ? (int64_t)metadata.st_mtime : 0;
}

bool rt_process_exists(int64_t pid) {
    if (pid <= 0) return false;
#if defined(_WIN32)
    HANDLE process = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, (DWORD)pid);
    if (!process) return GetLastError() == ERROR_ACCESS_DENIED;
    CloseHandle(process);
    return true;
#else
    return kill((pid_t)pid, 0) == 0 || errno == EPERM;
#endif
}

/* ELF spellings emitted by the self-hosted method fallback. Keep these as
 * compatibility aliases while MIR lowering converges on the libm names. */
#if !defined(_WIN32)
double rt_f64_sqrt(double value) __asm__("f64.sqrt");
double rt_f64_floor(double value) __asm__("f64.floor");
double rt_f64_ceil(double value) __asm__("f64.ceil");
double rt_f64_sqrt(double value) { return sqrt(value); }
double rt_f64_floor(double value) { return floor(value); }
double rt_f64_ceil(double value) { return ceil(value); }
#endif

int64_t max(int64_t left, int64_t right) {
    return left > right ? left : right;
}

int32_t rt_package_chmod(const uint8_t* path, uint64_t path_len, int32_t mode) {
#if defined(_WIN32)
    (void)path;
    (void)path_len;
    (void)mode;
    return 0;
#else
    if (!path || path_len == 0 || path_len >= 4096) return -1;
    char buffer[4096];
    memcpy(buffer, path, (size_t)path_len);
    buffer[path_len] = '\0';
    return chmod(buffer, (mode_t)mode) == 0 ? 0 : -1;
#endif
}
