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

static int secure_copy_path(const uint8_t* ptr, uint64_t len, char* out, size_t cap) {
    if (!ptr || !out || len == 0 || len >= cap || memchr(ptr, 0, (size_t)len)) return 0;
    memcpy(out, ptr, (size_t)len); out[len] = 0; return 1;
}

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
    if (!fill || fill(NULL, random, sizeof(random), 2) < 0) { if (bcrypt) FreeLibrary(bcrypt); return rt_string_new(NULL, 0); }
    FreeLibrary(bcrypt); char suffix[33];
    for (size_t i = 0; i < sizeof(random); i++) snprintf(suffix + i * 2, 3, "%02x", random[i]);
    int n = snprintf(path, sizeof(path), "%s\\%s-%s", parent, prefix, suffix);
    HMODULE advapi = LoadLibraryA("advapi32.dll"); PSECURITY_DESCRIPTOR descriptor = NULL;
    SddlFn convert = advapi ? (SddlFn)GetProcAddress(advapi, "ConvertStringSecurityDescriptorToSecurityDescriptorA") : NULL;
    if (n < 0 || (size_t)n >= sizeof(path) || !convert || !convert("D:P(A;;FA;;;SY)(A;;FA;;;OW)", 1, &descriptor, NULL)) { if (advapi) FreeLibrary(advapi); return rt_string_new(NULL, 0); }
    SECURITY_ATTRIBUTES attributes = { sizeof(attributes), descriptor, FALSE };
    BOOL created = CreateDirectoryA(path, &attributes); LocalFree(descriptor); FreeLibrary(advapi);
    if (!created) return rt_string_new(NULL, 0);
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
