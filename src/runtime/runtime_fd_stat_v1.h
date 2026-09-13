#ifndef SIMPLE_RUNTIME_FD_STAT_V1_H
#define SIMPLE_RUNTIME_FD_STAT_V1_H

#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#if !defined(_WIN32_WINNT) || _WIN32_WINNT < 0x0602
#undef _WIN32_WINNT
#define _WIN32_WINNT 0x0602
#endif
#include <io.h>
#include <windows.h>
#else
#include <sys/stat.h>
#include <unistd.h>
#endif

#define RT_FD_STAT_V1_WORDS 10
#define RT_FD_STAT_V1_BYTES (RT_FD_STAT_V1_WORDS * sizeof(uint64_t))

enum rt_fd_stat_kind_v1 {
    RT_FD_STAT_KIND_V1_REGULAR = 1,
    RT_FD_STAT_KIND_V1_DIRECTORY = 2,
    RT_FD_STAT_KIND_V1_OTHER = 3
};

#if defined(_WIN32) && defined(_MSC_VER)
static void __cdecl rt_fd_stat_ignore_invalid_parameter_v1(
    const wchar_t *expression, const wchar_t *function,
    const wchar_t *file, unsigned int line, uintptr_t reserved) {
    (void)expression;
    (void)function;
    (void)file;
    (void)line;
    (void)reserved;
}
#endif

/*
 * Sample identity and extent from an already-open descriptor.  The descriptor
 * remains borrowed by the caller.  One fstat(2), or the Windows identity,
 * standard, and basic queries on that same stable handle, supplies the fields;
 * no pathname is consulted after open.
 *
 * The caller must keep the descriptor open and must not concurrently close or
 * reuse it until this call returns.  This snapshot prevents pathname
 * replacement and validates the extent observed before mapping; it is not a
 * write lease and cannot prevent a separate writer from truncating afterward.
 * A loader facing hostile writers must additionally deny writes, copy into an
 * owned immutable artifact, or use a platform lease before mapping.
 *
 * Output words:
 *   0 filesystem/volume id, 1 object id low, 2 object id high,
 *   3 byte size, 4 allocated bytes, 5 mode/attributes, 6 link count,
 *   7 modified ns, 8 changed ns, 9 rt_fd_stat_kind_v1.
 *
 * Returns zero on success or a negative errno-style value.  Once the exact
 * output extent is validated, it is zeroed and is published only after the
 * platform metadata query sequence and all overflow checks succeed.
 */
#if !defined(_WIN32)
static int rt_fd_stat_ns_v1(int64_t seconds, int64_t nanos, uint64_t *out) {
    if (!out || nanos < 0 || nanos >= INT64_C(1000000000)) return 0;
    if (seconds < 0) { *out = 0; return 1; }
    if ((uint64_t)seconds > UINT64_MAX / UINT64_C(1000000000)) return 0;
    uint64_t base = (uint64_t)seconds * UINT64_C(1000000000);
    if (base > UINT64_MAX - (uint64_t)nanos) return 0;
    *out = base + (uint64_t)nanos;
    return 1;
}
#endif

static int64_t rt_fd_stat_snapshot_v1_impl(
    int64_t descriptor, uint64_t *out_words, int64_t out_bytes) {
    uint64_t snapshot[RT_FD_STAT_V1_WORDS] = {0};
    if (!out_words || out_bytes != (int64_t)RT_FD_STAT_V1_BYTES) return -EINVAL;
    memset(out_words, 0, RT_FD_STAT_V1_BYTES);

#if defined(_WIN32)
    if (descriptor < 0 || descriptor > INT32_MAX) return -EBADF;
#if !defined(_MSC_VER)
    /* MinGW CRT families do not provide a uniform non-terminating invalid-fd
     * query.  Refuse this lane until its descriptor owner supplies one. */
    return -ENOTSUP;
#else
    intptr_t native;
    _invalid_parameter_handler prior_handler =
        _set_thread_local_invalid_parameter_handler(
            rt_fd_stat_ignore_invalid_parameter_v1);
    native = _get_osfhandle((int)descriptor);
    _set_thread_local_invalid_parameter_handler(prior_handler);
    if (native == -1) return -EBADF;

    FILE_ID_INFO identity;
    FILE_STANDARD_INFO standard;
    FILE_BASIC_INFO basic;
    memset(&identity, 0, sizeof(identity));
    memset(&standard, 0, sizeof(standard));
    memset(&basic, 0, sizeof(basic));
    if (!GetFileInformationByHandleEx((HANDLE)native, FileIdInfo,
            &identity, sizeof(identity)) ||
        !GetFileInformationByHandleEx((HANDLE)native, FileStandardInfo,
            &standard, sizeof(standard)) ||
        !GetFileInformationByHandleEx((HANDLE)native, FileBasicInfo,
            &basic, sizeof(basic))) {
        DWORD code = GetLastError();
        return code == ERROR_INVALID_HANDLE ? -EBADF : -EIO;
    }
    if (standard.EndOfFile.QuadPart < 0 ||
        (uint64_t)standard.EndOfFile.QuadPart > INT64_MAX ||
        standard.AllocationSize.QuadPart < 0) return -EOVERFLOW;
    uint64_t size = (uint64_t)standard.EndOfFile.QuadPart;
    snapshot[0] = (uint64_t)identity.VolumeSerialNumber;
    memcpy(&snapshot[1], &identity.FileId.Identifier[0], sizeof(uint64_t));
    memcpy(&snapshot[2], &identity.FileId.Identifier[8], sizeof(uint64_t));
    snapshot[3] = size;
    snapshot[4] = (uint64_t)standard.AllocationSize.QuadPart;
    snapshot[5] = (uint64_t)basic.FileAttributes;
    snapshot[6] = (uint64_t)standard.NumberOfLinks;
    uint64_t write_ticks = (uint64_t)basic.LastWriteTime.QuadPart;
    uint64_t change_ticks = (uint64_t)basic.ChangeTime.QuadPart;
    const uint64_t windows_to_unix_100ns = UINT64_C(116444736000000000);
    if (write_ticks >= windows_to_unix_100ns) {
        uint64_t unix_ticks = write_ticks - windows_to_unix_100ns;
        if (unix_ticks > UINT64_MAX / UINT64_C(100)) return -EOVERFLOW;
        snapshot[7] = unix_ticks * UINT64_C(100);
    }
    if (change_ticks >= windows_to_unix_100ns) {
        uint64_t unix_ticks = change_ticks - windows_to_unix_100ns;
        if (unix_ticks > UINT64_MAX / UINT64_C(100)) return -EOVERFLOW;
        snapshot[8] = unix_ticks * UINT64_C(100);
    }
    snapshot[9] = standard.Directory
        ? RT_FD_STAT_KIND_V1_DIRECTORY : RT_FD_STAT_KIND_V1_REGULAR;
#endif
#else
    struct stat info;
    int rc;
    if (descriptor < 0 || descriptor > INT32_MAX) return -EBADF;
    do { rc = fstat((int)descriptor, &info); } while (rc != 0 && errno == EINTR);
    if (rc != 0) return -(int64_t)(errno ? errno : EIO);
    if (info.st_size < 0 || (uintmax_t)info.st_size > (uintmax_t)INT64_MAX)
        return -EOVERFLOW;
    snapshot[0] = (uint64_t)info.st_dev;
    snapshot[1] = (uint64_t)info.st_ino;
    snapshot[2] = 0;
    snapshot[3] = (uint64_t)info.st_size;
    if (info.st_blocks > 0 && (uintmax_t)info.st_blocks <= UINT64_MAX / 512u)
        snapshot[4] = (uint64_t)info.st_blocks * UINT64_C(512);
    snapshot[5] = (uint64_t)info.st_mode;
    snapshot[6] = (uint64_t)info.st_nlink;
  #if defined(__APPLE__)
    if (!rt_fd_stat_ns_v1((int64_t)info.st_mtimespec.tv_sec,
            (int64_t)info.st_mtimespec.tv_nsec, &snapshot[7]) ||
        !rt_fd_stat_ns_v1((int64_t)info.st_ctimespec.tv_sec,
            (int64_t)info.st_ctimespec.tv_nsec, &snapshot[8])) return -EOVERFLOW;
  #else
    if (!rt_fd_stat_ns_v1((int64_t)info.st_mtim.tv_sec,
            (int64_t)info.st_mtim.tv_nsec, &snapshot[7]) ||
        !rt_fd_stat_ns_v1((int64_t)info.st_ctim.tv_sec,
            (int64_t)info.st_ctim.tv_nsec, &snapshot[8])) return -EOVERFLOW;
  #endif
    snapshot[9] = S_ISREG(info.st_mode) ? RT_FD_STAT_KIND_V1_REGULAR :
        (S_ISDIR(info.st_mode) ? RT_FD_STAT_KIND_V1_DIRECTORY :
         RT_FD_STAT_KIND_V1_OTHER);
#endif
    if (snapshot[1] == 0 && snapshot[2] == 0) return -EIO;
    memcpy(out_words, snapshot, RT_FD_STAT_V1_BYTES);
    return 0;
}

#endif
