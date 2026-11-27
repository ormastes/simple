/* Shared narrow host provider (native core-C bundle). The Rust seed archive gets its definition from the Rust twin in file_ops.rs, not from this file.
 * The value/text accessors are public ABI; no C or Rust heap layout is assumed.
 */
#include "runtime.h"
#include "runtime_disk_headroom_private.h"
#include <string.h>
#if defined(_WIN32)
#include <windows.h>
#elif defined(__unix__) || defined(__APPLE__)
#include <sys/statvfs.h>
#endif

int64_t rt_host_disk_headroom_bytes_v1(int64_t path_value) {
    int64_t length = rt_string_len(path_value);
    const uint8_t *data = rt_string_data(path_value);
    if (length <= 0 || length >= 4096 || !data || memchr(data, 0, (size_t)length)) return 0;
#if defined(_WIN32)
    WCHAR wide[4096];
    int converted = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS,
        (LPCCH)data, (int)length, wide, 4095);
    if (converted <= 0) return 0;
    wide[converted] = L'\0';
    ULARGE_INTEGER free_for_caller = {0};
    if (!GetDiskFreeSpaceExW(wide, &free_for_caller, NULL, NULL)) return 0;
    return rt_disk_headroom_product_v1(free_for_caller.QuadPart, 1);
#elif defined(__unix__) || defined(__APPLE__)
    char narrow[4096];
    memcpy(narrow, data, (size_t)length);
    narrow[length] = '\0';
    struct statvfs stat_buf;
    if (statvfs(narrow, &stat_buf) != 0) return 0;
    return rt_disk_headroom_product_v1((uint64_t)stat_buf.f_bavail,
        (uint64_t)stat_buf.f_frsize);
#else
    return 0;
#endif
}
