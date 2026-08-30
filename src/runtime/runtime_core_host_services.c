/* Narrow hosted providers required by core-c-bootstrap tool closures.
 *
 * Keep these out of runtime_native.c: that translation unit is also used by
 * freestanding lanes.  The core-C capsule opts into this file explicitly.
 */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif
/* _POSIX_C_SOURCE alone hides the host extensions this file needs
 * (_SC_NPROCESSORS_ONLN, arc4random_buf on Darwin/BSD).  Re-open the platform
 * namespace explicitly rather than dropping the POSIX baseline. */
#if defined(__APPLE__)
#ifndef _DARWIN_C_SOURCE
#define _DARWIN_C_SOURCE 1
#endif
#elif defined(__linux__)
#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE 1
#endif
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
#include <bcrypt.h>
#include <sys/stat.h>
#undef max
#else
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <sys/wait.h>
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

/* ---------------------------------------------------------------------------
 * Additional narrow hosted providers (2026-08-30).
 *
 * ABI note: in this translation unit a Simple `text` PARAMETER lowers to the
 * pair (const uint8_t* ptr, uint64_t len) -- see rt_file_stat and
 * rt_package_chmod above -- and a `text` RETURN is a malloc'd char* (see
 * rt_hostname).  This is the native/core-C-capsule ABI, NOT the interpreter
 * ABI used by runtime_dynload.c (int64_t handle + rt_interp_cstr).  Do not mix
 * the two.
 *
 * Every function below fails LOUDLY (negative sentinel, or NULL for text)
 * rather than returning a plausible-looking substitute.  A fabricated CPU
 * count or a predictable UUID is worse than an absent symbol.
 * ------------------------------------------------------------------------- */

/* Online CPU count.  Returns -1 when the host cannot report it; callers must
 * not silently substitute 1. */
int64_t rt_cpu_count(void) {
#if defined(_WIN32)
    SYSTEM_INFO info;
    GetSystemInfo(&info);
    return info.dwNumberOfProcessors > 0 ? (int64_t)info.dwNumberOfProcessors : -1;
#else
    long count = sysconf(_SC_NPROCESSORS_ONLN);
    return count > 0 ? (int64_t)count : -1;
#endif
}

/* File modification time as a Unix timestamp in whole seconds.
 * Semantics pinned by the two sffi_gen specs that declare this symbol
 * (src/app/ffi_gen.specs/file_io.spl:93 and
 * src/compiler/90.tools/sffi_gen/specs/file_io.spl:103):
 * "Get file modification time as unix timestamp".
 * Returns -1 on failure.  0 is NOT used as the failure sentinel here because
 * it is a legitimate mtime (the Unix epoch); the sibling rt_file_stat's use of
 * 0 conflates the two. */
int64_t rt_file_modified(const uint8_t* path, uint64_t path_len) {
    if (!path || path_len == 0 || path_len >= 4096) return -1;
    char buffer[4096];
    memcpy(buffer, path, (size_t)path_len);
    buffer[path_len] = '\0';
    struct stat metadata;
    if (stat(buffer, &metadata) != 0) return -1;
    return (int64_t)metadata.st_mtime;
}

/* Write raw bytes to the process stdout, returning the number of bytes
 * written, or -1 on error.  Retries EINTR and short writes so the returned
 * count is truthful rather than optimistic. */
int64_t rt_term_write(const uint8_t* data, uint64_t data_len) {
    if (!data && data_len != 0) return -1;
    if (data_len == 0) return 0;
#if defined(_WIN32)
    DWORD written = 0;
    HANDLE out = GetStdHandle(STD_OUTPUT_HANDLE);
    if (out == INVALID_HANDLE_VALUE) return -1;
    if (data_len > (uint64_t)0x7fffffffu) return -1;
    if (!WriteFile(out, data, (DWORD)data_len, &written, NULL)) return -1;
    return (int64_t)written;
#else
    uint64_t offset = 0;
    while (offset < data_len) {
        ssize_t put = write(STDOUT_FILENO, data + offset,
                            (size_t)(data_len - offset));
        if (put < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        if (put == 0) break;
        offset += (uint64_t)put;
    }
    return (int64_t)offset;
#endif
}

/* Run a command through the host shell and return its EXIT STATUS.
 *
 * Deliberately NOT the raw system() return: system() yields a wait status in
 * which a normal exit of 1 is the value 256, which is exactly the class of
 * plausible-looking wrong value this runtime must not produce.  The sibling
 * spl_shell (runtime.c:1291) returns the raw wait status; that difference is
 * intentional and documented here rather than propagated.
 * Returns -1 when the command could not be run or did not exit normally. */
int64_t rt_shell(const uint8_t* cmd, uint64_t cmd_len) {
    if (!cmd || cmd_len == 0 || cmd_len >= 65536) return -1;
    char* buffer = (char*)malloc((size_t)cmd_len + 1);
    if (!buffer) return -1;
    memcpy(buffer, cmd, (size_t)cmd_len);
    buffer[cmd_len] = '\0';
    int status = system(buffer);
    free(buffer);
    if (status == -1) return -1;
#if defined(_WIN32)
    return (int64_t)status;
#else
    if (WIFEXITED(status)) return (int64_t)WEXITSTATUS(status);
    if (WIFSIGNALED(status)) return (int64_t)(128 + WTERMSIG(status));
    return -1;
#endif
}

/* RFC 4122 version-4 UUID from OS cryptographic entropy.
 *
 * Returns a malloc'd 36-character canonical string, or NULL when the host
 * refuses entropy.  NULL is deliberate: this symbol's declared callers include
 * src/compiler/80.driver/build_log.spl, where a predictable or fabricated UUID
 * would silently collide across build records.  There is no non-random
 * fallback on purpose. */
char* rt_uuid_v4(void) {
    uint8_t bytes[16];
#if defined(_WIN32)
    if (BCryptGenRandom(NULL, bytes, (ULONG)sizeof(bytes),
                        BCRYPT_USE_SYSTEM_PREFERRED_RNG) != 0) {
        return NULL;
    }
#elif defined(__APPLE__) || defined(__FreeBSD__) || defined(__OpenBSD__)
    /* arc4random_buf is a CSPRNG and is documented as always succeeding. */
    arc4random_buf(bytes, sizeof(bytes));
#else
    if (getentropy(bytes, sizeof(bytes)) != 0) return NULL;
#endif
    /* Version 4 (random) in the high nibble of byte 6; RFC 4122 variant in the
     * two high bits of byte 8. */
    bytes[6] = (uint8_t)((bytes[6] & 0x0f) | 0x40);
    bytes[8] = (uint8_t)((bytes[8] & 0x3f) | 0x80);

    static const char hex[] = "0123456789abcdef";
    char text[37];
    size_t out = 0;
    for (size_t i = 0; i < 16; i++) {
        if (i == 4 || i == 6 || i == 8 || i == 10) text[out++] = '-';
        text[out++] = hex[(bytes[i] >> 4) & 0x0f];
        text[out++] = hex[bytes[i] & 0x0f];
    }
    text[out] = '\0';
    return core_host_strdup(text);
}
