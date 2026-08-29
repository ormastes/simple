/* Narrow hosted providers required by core-c-bootstrap tool closures.
 *
 * Keep these out of runtime_native.c: that translation unit is also used by
 * freestanding lanes.  The core-C capsule opts into this file explicitly.
 */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif

#include "runtime.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#include <windows.h>
#else
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <unistd.h>
#endif

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
        return strdup(buffer);
    }
#endif
    return strdup("localhost");
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
