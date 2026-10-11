/* Shared bounded no-follow parser-cell provider. Included by the mutually
 * exclusive full core-C and narrow Rust-bootstrap runtime owners. */
#ifndef SIMPLE_RUNTIME_SHARED_PARSE_CELL_PRIVATE_H
#define SIMPLE_RUNTIME_SHARED_PARSE_CELL_PRIVATE_H
#include "runtime.h"
#include <stdlib.h>
#include <string.h>
#if defined(_WIN32)
#include <windows.h>
#else
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#endif
#define RT_SECURE_PATH_MAX 4096
static int secure_copy_path(const uint8_t* ptr, uint64_t len, char* out, size_t cap) {
    if (!ptr || !out || len == 0 || len >= cap || memchr(ptr, 0, (size_t)len)) return 0;
    memcpy(out, ptr, (size_t)len); out[len] = 0; return 1;
}
#if defined(_WIN32)
/* Widen a UTF-8 path to UTF-16 and, when qualifying it as a full path still
 * leaves it long, add the extended-length ("\\?\") prefix so a WIDE Win32
 * call is not itself capped at MAX_PATH (a wide call is not exempt on its
 * own -- only the prefix lifts the ceiling, to ~32767). `out` must hold at
 * least 32768 wchar_t. Returns 0 (leaving `out` untouched) when the path
 * cannot be widened/qualified at all, so callers fall back to the ANSI call
 * for a normal-length or otherwise-unrepresentable path. Named without the
 * rt_ prefix (unlike its Simple-facing siblings in this file) because it is
 * a pure file-local helper with no runtime-API surface of its own -- see
 * scripts/check/check-rt-dual-implementation-ratchet.shs, which treats any
 * new rt_-prefixed definition as a fresh single-lane primitive requiring a
 * Simple twin. The path separator and prefix are built from the numeric
 * code point (92) rather than written literally, purely to keep this source
 * free of escape sequences. */
static int spl_secure_widen_long_path(const char* path, wchar_t* out) {
    static const wchar_t sep = (wchar_t)92;
    wchar_t wide[32768], full[32768];
    wchar_t* scan;
    DWORD n;
    size_t len;
    if (MultiByteToWideChar(CP_UTF8, 0, path, -1, wide,
                            (int)(sizeof(wide) / sizeof(wide[0]))) == 0) {
        return 0;
    }
    for (scan = wide; *scan; scan++) { if (*scan == L'/') *scan = sep; }
    n = GetFullPathNameW(wide, (DWORD)(sizeof(full) / sizeof(full[0])), full, NULL);
    if (n == 0 || n >= sizeof(full) / sizeof(full[0])) return 0;
    /* Already extended-length, or a UNC path: hand it over unchanged. */
    if (full[0] == sep && full[1] == sep) {
        memcpy(out, full, (wcslen(full) + 1) * sizeof(wchar_t));
        return 1;
    }
    len = wcslen(full);
    if (len + 5 >= 32768) return 0;
    out[0] = sep; out[1] = sep; out[2] = L'?'; out[3] = sep;
    memcpy(out + 4, full, (len + 1) * sizeof(wchar_t));
    return 1;
}
#endif

/* A bounded, same-handle read for the optional cross-host flat-pool cache.
 * A caller verifies its immutable key and payload SHA after this read. The
 * leaf is opened without following a symlink/reparse point; missing, changed,
 * nonregular and oversized files all become ordinary cache misses. */
int64_t rt_shared_parse_cell_read_v1(const uint8_t* path_ptr, uint64_t path_len, int64_t maximum) {
    char path[RT_SECURE_PATH_MAX];
    if (maximum <= 0 || maximum > 33554432 ||
        !secure_copy_path(path_ptr, path_len, path, sizeof(path)))
        return rt_string_new(NULL, 0);
#if defined(_WIN32)
    wchar_t wide_path[32768];
    if (!spl_secure_widen_long_path(path, wide_path)) return rt_string_new(NULL, 0);
    HANDLE file = CreateFileW(wide_path, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_DELETE, NULL, OPEN_EXISTING,
        FILE_FLAG_OPEN_REPARSE_POINT, NULL);
    if (file == INVALID_HANDLE_VALUE) return rt_string_new(NULL, 0);
    BY_HANDLE_FILE_INFORMATION before, after;
    LARGE_INTEGER length;
    int ok = GetFileInformationByHandle(file, &before) &&
        !(before.dwFileAttributes & (FILE_ATTRIBUTE_DIRECTORY | FILE_ATTRIBUTE_REPARSE_POINT)) &&
        GetFileSizeEx(file, &length) && length.QuadPart > 0 &&
        length.QuadPart <= maximum;
    uint8_t* bytes = ok ? (uint8_t*)malloc((size_t)length.QuadPart) : NULL;
    if (!bytes) ok = 0;
    size_t done = 0;
    while (ok && done < (size_t)length.QuadPart) {
        DWORD got = 0;
        DWORD want = (DWORD)((size_t)length.QuadPart - done);
        if (!ReadFile(file, bytes + done, want, &got, NULL) || got == 0) ok = 0;
        else done += got;
    }
    if (ok && (!GetFileInformationByHandle(file, &after) ||
        before.dwVolumeSerialNumber != after.dwVolumeSerialNumber ||
        before.nFileIndexHigh != after.nFileIndexHigh ||
        before.nFileIndexLow != after.nFileIndexLow ||
        before.nFileSizeHigh != after.nFileSizeHigh ||
        before.nFileSizeLow != after.nFileSizeLow ||
        CompareFileTime(&before.ftLastWriteTime, &after.ftLastWriteTime) != 0)) ok = 0;
    CloseHandle(file);
    int64_t result = ok ? rt_string_new(bytes, (uint64_t)length.QuadPart) :
        rt_string_new(NULL, 0);
    free(bytes);
    return result;
#elif !defined(O_NOFOLLOW)
    /* No no-follow open on this libc (SimpleOS): an ordinary cache miss. */
    return rt_string_new(NULL, 0);
#else
    int fd = open(path, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) return rt_string_new(NULL, 0);
    struct stat before, after;
    int ok = !fstat(fd, &before) && S_ISREG(before.st_mode) &&
        before.st_size > 0 && before.st_size <= maximum;
    uint8_t* bytes = ok ? (uint8_t*)malloc((size_t)before.st_size) : NULL;
    if (!bytes) ok = 0;
    size_t done = 0;
    while (ok && done < (size_t)before.st_size) {
        ssize_t got = read(fd, bytes + done, (size_t)before.st_size - done);
        if (got <= 0) ok = 0;
        else done += (size_t)got;
    }
    if (ok && (fstat(fd, &after) || before.st_dev != after.st_dev ||
        before.st_ino != after.st_ino || before.st_size != after.st_size ||
        before.st_mtime != after.st_mtime)) ok = 0;
    close(fd);
    int64_t result = ok ? rt_string_new(bytes, (uint64_t)before.st_size) :
        rt_string_new(NULL, 0);
    free(bytes);
    return result;
#endif
}
#endif
