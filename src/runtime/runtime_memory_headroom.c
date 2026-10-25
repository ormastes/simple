/* Shared narrow host provider: also linked into the Rust runtime archive.
 * Preserve windows_capacity_headroom_v1 semantics: min(AvailPhys, AvailPageFile).
 */
#include "runtime.h"
#include <limits.h>
#include <string.h>
#if defined(_WIN32)
#include <windows.h>
#endif

int64_t rt_host_memory_headroom_bytes_v1(void) {
#if defined(_WIN32)
    MEMORYSTATUSEX status;
    memset(&status, 0, sizeof(status));
    status.dwLength = sizeof(status);
    if (!GlobalMemoryStatusEx(&status)) return 0;
    if (status.ullAvailPhys > (uint64_t)INT64_MAX) return 0;
    if (status.ullAvailPageFile > (uint64_t)INT64_MAX) return 0;
    uint64_t headroom = status.ullAvailPhys < status.ullAvailPageFile
        ? status.ullAvailPhys
        : status.ullAvailPageFile;
    return (int64_t)headroom;
#else
    return 0;
#endif
}
