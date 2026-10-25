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

/* Committed private memory of one live process, KiB; -1 when unknown.
 * Windows: PROCESS_MEMORY_COUNTERS_EX.PrivateUsage (what the commit limit
 * charges; working-set RSS under-reports it). Linux: VmRSS + VmSwap.
 * Shard coordinators sample children with it to admit by measured
 * footprint instead of a fixed estimate. */
#if defined(_WIN32)
#include <psapi.h>
#elif defined(__linux__)
#include <stdio.h>
#include <stdlib.h>
#endif
int64_t rt_process_private_kib_v1(int64_t pid) {
    if (pid <= 0) return -1;
#if defined(_WIN32)
    HANDLE h = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, (DWORD)pid);
    if (!h) return -1;
    HMODULE kernel32 = GetModuleHandleW(L"kernel32");
    typedef BOOL (WINAPI *QueryMemFn)(HANDLE, PPROCESS_MEMORY_COUNTERS, DWORD);
    QueryMemFn query = kernel32 ? (QueryMemFn)(void (*)(void))GetProcAddress(kernel32, "K32GetProcessMemoryInfo") : NULL;
    PROCESS_MEMORY_COUNTERS_EX pmc;
    memset(&pmc, 0, sizeof(pmc));
    pmc.cb = (DWORD)sizeof(pmc);
    BOOL ok = query ? query(h, (PPROCESS_MEMORY_COUNTERS)&pmc, (DWORD)sizeof(pmc)) : FALSE;
    CloseHandle(h);
    if (!ok) return -1;
    return (int64_t)(pmc.PrivateUsage / 1024);
#elif defined(__linux__)
    char path[64];
    snprintf(path, sizeof(path), "/proc/%lld/status", (long long)pid);
    FILE* f = fopen(path, "r");
    if (!f) return -1;
    char line[256];
    int64_t rss = -1, swap = 0;
    while (fgets(line, sizeof(line), f)) {
        if (strncmp(line, "VmRSS:", 6) == 0) rss = strtoll(line + 6, NULL, 10);
        else if (strncmp(line, "VmSwap:", 7) == 0) swap = strtoll(line + 7, NULL, 10);
    }
    fclose(f);
    return rss < 0 ? -1 : rss + swap;
#else
    return -1;
#endif
}

/* System commit headroom, KiB; -1 when unknown. Windows: ullAvailPageFile
 * (CommitLimit - CommitTotal). Linux: MemAvailable + SwapFree. */
int64_t rt_host_commit_avail_kib_v1(void) {
#if defined(_WIN32)
    MEMORYSTATUSEX status;
    memset(&status, 0, sizeof(status));
    status.dwLength = sizeof(status);
    if (!GlobalMemoryStatusEx(&status)) return -1;
    return (int64_t)(status.ullAvailPageFile / 1024);
#elif defined(__linux__)
    FILE* f = fopen("/proc/meminfo", "r");
    if (!f) return -1;
    char line[256];
    int64_t avail = -1, swap = 0;
    while (fgets(line, sizeof(line), f)) {
        if (strncmp(line, "MemAvailable:", 13) == 0) avail = strtoll(line + 13, NULL, 10);
        else if (strncmp(line, "SwapFree:", 9) == 0) swap = strtoll(line + 9, NULL, 10);
    }
    fclose(f);
    return avail < 0 ? -1 : avail + swap;
#else
    return -1;
#endif
}
