/* Retained query storage belongs to the Simple child stdio IO owner. No
 * allocation, HANDLE acquisition, process registry or linker ntdll dependency. */
#ifndef SIMPLE_WINDOWS_PIPE_FILE_MODE_PRIVATE_V1_H
#define SIMPLE_WINDOWS_PIPE_FILE_MODE_PRIVATE_V1_H
#include <stdint.h>
#if defined(_WIN32)
#include <windows.h>
#include <winternl.h>
typedef struct {
    IO_STATUS_BLOCK status;
    ULONG mode; /* Documented FILE_MODE_INFORMATION's sole ULONG member. */
} SimplePipeFileModeQueryV1;
typedef NTSTATUS (NTAPI *SimplePipeQueryInformationV1)(HANDLE, PIO_STATUS_BLOCK,
    PVOID, ULONG, FILE_INFORMATION_CLASS);
typedef char SimplePipeQueryStorageFitsV1[sizeof(SimplePipeFileModeQueryV1) <= 64 ? 1 : -1];

int64_t rt_windows_pipe_file_mode_v1(int64_t handle, int64_t storage,
        int64_t mode_out, int32_t operation) {
    if (!handle || !storage || !mode_out || ((uint64_t)storage & 7) ||
            ((uint64_t)mode_out & 3) || (operation != 0 && operation != 1)) return -1;
    SimplePipeFileModeQueryV1 *query = (SimplePipeFileModeQueryV1 *)(intptr_t)storage;
    LONG status;
    if (operation == 0) {
        HMODULE module = GetModuleHandleW(L"ntdll.dll");
        SimplePipeQueryInformationV1 query_info = module ?
            (SimplePipeQueryInformationV1)(void *)GetProcAddress(module, "NtQueryInformationFile") : NULL;
        if (!query_info) return -1;
        ZeroMemory(query, sizeof(*query));
        query->status.Status = (NTSTATUS)259; /* STATUS_PENDING */
        status = query_info((HANDLE)(intptr_t)handle, &query->status, &query->mode,
            sizeof(query->mode), (FILE_INFORMATION_CLASS)16); /* FileModeInformation */
    } else {
        /* This handle has no other operation during admission. Observe actual
         * handle completion before reading the IOSB, as required by the NT
         * query contract. Timeout, failed wait and unknown observations all
         * retain the query; no blocking wait or cancellation-as-proof. */
        DWORD observed = WaitForSingleObject((HANDLE)(intptr_t)handle, 0);
        if (observed != WAIT_OBJECT_0) return 259;
        status = InterlockedCompareExchange((volatile LONG *)&query->status.Status, 0, 0);
    }
    if (status == 259) return 259;
    if (status != 0) return status < 0 ? (int64_t)status : -1;
    if (query->status.Information != sizeof(query->mode)) return -1;
    *(ULONG *)(intptr_t)mode_out = query->mode;
    return 0;
}
#else
int64_t rt_windows_pipe_file_mode_v1(int64_t handle, int64_t storage,
        int64_t mode_out, int32_t operation) {
    (void)handle; (void)storage; (void)mode_out; (void)operation;
    return -1;
}
#endif
#endif
