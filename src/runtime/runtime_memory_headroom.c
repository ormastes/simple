/* Shared narrow host provider: also linked into the Rust runtime archive.
 * Preserve windows_capacity_headroom_v1 semantics: min(AvailPhys, AvailPageFile).
 */
#include "runtime.h"
#include <limits.h>
#include <string.h>
#if defined(_WIN32)
#include <windows.h>
#include <psapi.h>
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

/* Commit headroom (CommitLimit - CommitTotal) * PageSize via
 * K32GetPerformanceInfo, resolved with GetProcAddress because the symbol
 * lives in kernel32 on modern Windows. Use the SDK's typed layout: PageSize is at
 * offset 80 on Win64; offset 88 contains HandleCount and ProcessCount.
 * Same interpreter-first rationale as rt_host_memory_headroom_bytes_v1.
 * Returns 0 when unavailable; callers keep the extern path as fallback. */
int64_t rt_host_commit_headroom_bytes_v1(void) {
#if defined(_WIN32)
    HMODULE kernel32 = GetModuleHandleW(L"kernel32");
    if (!kernel32) return 0;
    typedef BOOL (WINAPI *QueryCommitFn)(PPERFORMANCE_INFORMATION, DWORD);
    QueryCommitFn query = (QueryCommitFn)(void (*)(void))GetProcAddress(kernel32, "K32GetPerformanceInfo");
    if (!query) return 0;
    PERFORMANCE_INFORMATION info;
    memset(&info, 0, sizeof(info));
    info.cb = (uint32_t)sizeof(info);
    if (query(&info, (DWORD)sizeof(info)) == 0) return 0;
    uint64_t commit_total = info.CommitTotal;
    uint64_t commit_limit = info.CommitLimit;
    uint64_t page_size = info.PageSize;
    if (commit_limit < commit_total || page_size == 0) return 0;
    uint64_t headroom_pages = commit_limit - commit_total;
    if (headroom_pages > (uint64_t)INT64_MAX / page_size) return 0;
    return (int64_t)(headroom_pages * page_size);
#else
    return 0;
#endif
}
