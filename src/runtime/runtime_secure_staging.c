/* Narrow provider for Rust Stage2 archives, which intentionally omit
 * runtime.c/runtime_native.c to avoid duplicate ownership of other rt_* APIs. */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include "runtime.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(_WIN32)
#include <windows.h>
#else
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#if defined(__linux__)
#include <sys/syscall.h>
#endif
#endif

#define RT_SECURE_PATH_MAX 4096

/* These four functions are needed by bootstrap_main but their historical
 * owners (runtime.c/runtime_native.c) cannot be compiled into native_all:
 * they collide with hundreds of Rust-owned rt_* definitions.  Keep the
 * native_all-only mirrors in this deliberately narrow translation unit. */
int64_t rt_simple_abi_version(void) {
    return (int64_t)SIMPLE_ABI_VERSION;
}

int64_t rt_simple_abi_version_deferred(void) {
    return SIMPLE_ABI_VERSION_DEFERRED ? 1 : 0;
}

static int secure_copy_path(const uint8_t* ptr, uint64_t len, char* out, size_t cap) {
    if (!ptr || !out || len == 0 || len >= cap || memchr(ptr, 0, (size_t)len)) return 0;
    memcpy(out, ptr, (size_t)len); out[len] = 0; return 1;
}

int rt_file_create_excl(const char* path_ptr, int64_t path_len,
                        const char* content_ptr, int64_t content_len) {
    char path[RT_SECURE_PATH_MAX];
    if (path_len <= 0 || content_len < 0 ||
        !secure_copy_path((const uint8_t*)path_ptr, (uint64_t)path_len,
                          path, sizeof(path)) ||
        (content_len > 0 && !content_ptr)) return 0;
#if defined(_WIN32)
    HANDLE file = CreateFileA(path, GENERIC_WRITE, 0, NULL, CREATE_NEW,
                              FILE_ATTRIBUTE_NORMAL, NULL);
    if (file == INVALID_HANDLE_VALUE) return 0;
    DWORD written = 0;
    int ok = content_len <= (int64_t)UINT32_MAX;
    if (ok && content_len > 0)
        ok = WriteFile(file, content_ptr, (DWORD)content_len, &written, NULL) &&
            written == (DWORD)content_len;
    if (!CloseHandle(file)) ok = 0;
    return ok;
#else
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0600);
    if (fd < 0) return 0;
    int64_t done = 0;
    while (done < content_len) {
        ssize_t n = write(fd, content_ptr + done, (size_t)(content_len - done));
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) break;
        done += n;
    }
    int ok = done == content_len && close(fd) == 0;
    if (!ok) { if (done != content_len) close(fd); unlink(path); }
    return ok;
#endif
}

int rt_file_sync(const uint8_t* path_ptr, uint64_t path_len) {
    char path[RT_SECURE_PATH_MAX];
    if (!secure_copy_path(path_ptr, path_len, path, sizeof(path))) return 0;
#if defined(_WIN32)
    HANDLE file = CreateFileA(path, GENERIC_READ | GENERIC_WRITE,
                              FILE_SHARE_READ, NULL, OPEN_EXISTING,
                              FILE_ATTRIBUTE_NORMAL, NULL);
    if (file == INVALID_HANDLE_VALUE) return 0;
    int ok = FlushFileBuffers(file);
    if (!CloseHandle(file)) ok = 0;
    return ok;
#else
    int fd = open(path, O_RDWR | O_CLOEXEC);
    if (fd < 0) return 0;
    int ok = fsync(fd) == 0;
    if (close(fd) != 0) ok = 0;
    return ok;
#endif
}

#if defined(_WIN32)
/* Canonical implementation of the secure-staging pair (this file's own header
 * says "implemented once, in C"). Every Windows failure mode returned an empty
 * string, so the AOT diagnostic-staging caller could only ever say "diagnostic
 * staging unavailable". Name the failing step and the Win32 error.
 * SIMPLE_QUIET_SECURE_TEMP_DIAG=1 silences. */
static void rt_secure_temp_dir_diag(const char* stage, const char* detail) {
    if (getenv("SIMPLE_QUIET_SECURE_TEMP_DIAG")) return;
    fprintf(stderr, "rt_secure_temp_dir: %s failed (GetLastError=%lu) %s\n",
            stage, (unsigned long)GetLastError(), detail ? detail : "");
    fflush(stderr);
}
#endif

int64_t rt_secure_temp_dir(const uint8_t* parent_ptr, uint64_t parent_len,
                           const uint8_t* prefix_ptr, uint64_t prefix_len) {
    char parent[RT_SECURE_PATH_MAX], prefix[128], path[RT_SECURE_PATH_MAX];
    if (!secure_copy_path(parent_ptr, parent_len, parent, sizeof(parent)) ||
        !secure_copy_path(prefix_ptr, prefix_len, prefix, sizeof(prefix)) ||
        strchr(prefix, '/') || strchr(prefix, '\\')) return rt_string_new(NULL, 0);
#if defined(_WIN32)
    typedef LONG (WINAPI *RandomFn)(void*, unsigned char*, unsigned long, unsigned long);
    typedef BOOL (WINAPI *SddlFn)(const char*, DWORD, PSECURITY_DESCRIPTOR*, ULONG*);
    HMODULE bcrypt = LoadLibraryA("bcrypt.dll"); unsigned char random[16];
    RandomFn fill = bcrypt ? (RandomFn)GetProcAddress(bcrypt, "BCryptGenRandom") : NULL;
    if (!fill || fill(NULL, random, sizeof(random), 2) < 0) { rt_secure_temp_dir_diag("BCryptGenRandom", parent); if (bcrypt) FreeLibrary(bcrypt); return rt_string_new(NULL, 0); }
    FreeLibrary(bcrypt); char suffix[33];
    for (size_t i = 0; i < sizeof(random); i++) snprintf(suffix + i * 2, 3, "%02x", random[i]);
    int n = snprintf(path, sizeof(path), "%s\\%s-%s", parent, prefix, suffix);
    HMODULE advapi = LoadLibraryA("advapi32.dll"); PSECURITY_DESCRIPTOR descriptor = NULL;
    SddlFn convert = advapi ? (SddlFn)GetProcAddress(advapi, "ConvertStringSecurityDescriptorToSecurityDescriptorA") : NULL;
    if (n < 0 || (size_t)n >= sizeof(path) || !convert || !convert("D:P(A;;FA;;;SY)(A;;FA;;;OW)", 1, &descriptor, NULL)) { rt_secure_temp_dir_diag("ConvertStringSecurityDescriptor", path); if (advapi) FreeLibrary(advapi); return rt_string_new(NULL, 0); }
    SECURITY_ATTRIBUTES attributes = { sizeof(attributes), descriptor, FALSE };
    BOOL created = CreateDirectoryA(path, &attributes); LocalFree(descriptor); FreeLibrary(advapi);
    if (!created) { rt_secure_temp_dir_diag("CreateDirectoryA", path); return rt_string_new(NULL, 0); }
#else
    int n = snprintf(path, sizeof(path), "%s/%s-XXXXXX", parent, prefix);
    if (n < 0 || (size_t)n >= sizeof(path) || !mkdtemp(path)) return rt_string_new(NULL, 0);
    if (chmod(path, 0700) != 0) { rmdir(path); return rt_string_new(NULL, 0); }
#endif
    return rt_string_new((const uint8_t*)path, (uint64_t)strlen(path));
}

int64_t rt_file_publish_noreplace(const uint8_t* staged_ptr, uint64_t staged_len,
                                  const uint8_t* destination_ptr, uint64_t destination_len) {
    char staged[RT_SECURE_PATH_MAX], destination[RT_SECURE_PATH_MAX];
    if (!secure_copy_path(staged_ptr, staged_len, staged, sizeof(staged)) ||
        !secure_copy_path(destination_ptr, destination_len, destination, sizeof(destination))) return -1;
#if defined(_WIN32)
    if (MoveFileExA(staged, destination, MOVEFILE_WRITE_THROUGH)) return 1;
    DWORD error = GetLastError(); return (error == ERROR_ALREADY_EXISTS || error == ERROR_FILE_EXISTS) ? 0 : -1;
#else
#if defined(__linux__) && defined(SYS_renameat2)
    if (syscall(SYS_renameat2, AT_FDCWD, staged, AT_FDCWD, destination, 1) == 0) return 1;
    if (errno == EEXIST) return 0;
    if (errno != ENOSYS && errno != EINVAL) return -1;
#endif
    if (link(staged, destination) != 0) return errno == EEXIST ? 0 : -1;
    (void)unlink(staged); return 1;
#endif
}
