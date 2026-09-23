#ifndef SPL_WINDOWS_RAW_MAPPING_H
#define SPL_WINDOWS_RAW_MAPPING_H

#if !defined(_WIN32)
#error "windows_raw_mapping.h is Windows-only"
#endif

#include <stdint.h>
#include <limits.h>
#include <io.h>
#include <stdlib.h>
#include <windows.h>

#if defined(_MSC_VER)
static void __cdecl spl_windows_ignore_invalid_parameter(
        const wchar_t* expression, const wchar_t* function,
        const wchar_t* file, unsigned int line, uintptr_t reserved) {
    (void)expression;
    (void)function;
    (void)file;
    (void)line;
    (void)reserved;
}
#endif

static inline intptr_t spl_windows_os_handle(int fd) {
#if defined(_MSC_VER)
    _invalid_parameter_handler previous =
        _set_thread_local_invalid_parameter_handler(
            spl_windows_ignore_invalid_parameter);
    const intptr_t handle = _get_osfhandle(fd);
    _set_thread_local_invalid_parameter_handler(previous);
    return handle;
#else
    return _get_osfhandle(fd);
#endif
}

/* Shared Windows implementation behind the raw mmap ABI used by the SMF
 * loader. Anonymous mappings are VirtualAlloc reservations. File mappings
 * retain the caller's CRT descriptor only for CreateFileMapping; the mapped
 * view remains valid after both that descriptor and the section handle close.
 */
static inline int64_t spl_windows_mmap_raw(
        int64_t addr, int64_t length, int64_t prot, int64_t flags,
        int64_t fd, int64_t offset) {
    if (length <= 0 || offset < 0) return -1;
    if ((prot & 0x6) == 0x6) return -1; /* PROT_WRITE | PROT_EXEC */
    if ((prot & ~0x7LL) != 0) return -1;

    if (fd == -1) {
        DWORD protect;
        if (prot == 0x0) protect = PAGE_NOACCESS;
        else if (prot == 0x1) protect = PAGE_READONLY;
        else if (prot == 0x2 || prot == 0x3) protect = PAGE_READWRITE;
        else if (prot == 0x4) protect = PAGE_EXECUTE;
        else if (prot == 0x5) protect = PAGE_EXECUTE_READ;
        else return -1;
        void* result = VirtualAlloc((void*)(uintptr_t)addr, (SIZE_T)length,
                                    MEM_COMMIT | MEM_RESERVE, protect);
        return result ? (int64_t)(uintptr_t)result : -1;
    }

    if (fd < 0 || fd > INT_MAX) return -1;
    const int shared = (flags & 0x1) != 0;  /* MAP_SHARED */
    const int private_map = (flags & 0x2) != 0; /* MAP_PRIVATE */
    if (shared == private_map) return -1;

    SYSTEM_INFO system_info;
    GetSystemInfo(&system_info);
    if (system_info.dwAllocationGranularity == 0 ||
        ((uint64_t)offset % (uint64_t)system_info.dwAllocationGranularity) != 0) {
        return -1;
    }

    const intptr_t os_handle = spl_windows_os_handle((int)fd);
    if (os_handle == (intptr_t)-1) return -1;

    DWORD section_protect;
    DWORD view_access;
    if ((prot & 0x2) != 0) { /* PROT_WRITE; W+X was rejected above. */
        section_protect = private_map ? PAGE_WRITECOPY : PAGE_READWRITE;
        view_access = private_map ? FILE_MAP_COPY : FILE_MAP_WRITE;
    } else if ((prot & 0x4) != 0) {
        section_protect = PAGE_EXECUTE_READ;
        view_access = FILE_MAP_READ | FILE_MAP_EXECUTE;
    } else {
        section_protect = PAGE_READONLY;
        view_access = FILE_MAP_READ;
    }

    HANDLE section = CreateFileMappingA(
        (HANDLE)os_handle, NULL, section_protect, 0, 0, NULL);
    if (!section) return -1;

    DWORD offset_high = (DWORD)(((uint64_t)offset) >> 32);
    DWORD offset_low = (DWORD)(((uint64_t)offset) & 0xffffffffULL);
    void* result = MapViewOfFileEx(
        section, view_access, offset_high, offset_low, (SIZE_T)length,
        addr == 0 ? NULL : (void*)(uintptr_t)addr);
    CloseHandle(section);
    if (!result) return -1;

    DWORD final_protect = 0;
    if (prot == 0x0) final_protect = PAGE_NOACCESS;
    else if (prot == 0x2) {
        final_protect = private_map ? PAGE_WRITECOPY : PAGE_READWRITE;
    }
    else if (prot == 0x4) final_protect = PAGE_EXECUTE;
    if (final_protect != 0) {
        DWORD old_protect;
        if (!VirtualProtect(result, (SIZE_T)length, final_protect, &old_protect)) {
            UnmapViewOfFile(result);
            return -1;
        }
    }
    if ((prot & 0x4) != 0 &&
        !FlushInstructionCache(GetCurrentProcess(), result, (SIZE_T)length)) {
        UnmapViewOfFile(result);
        return -1;
    }
    return (int64_t)(uintptr_t)result;
}

static inline int64_t spl_windows_munmap_raw(int64_t addr, int64_t length) {
    if (!addr || length <= 0) return -1;
    MEMORY_BASIC_INFORMATION info;
    if (VirtualQuery((void*)(uintptr_t)addr, &info, sizeof(info)) == 0) return -1;
    if (info.Type == MEM_MAPPED || info.Type == MEM_IMAGE) {
        return UnmapViewOfFile((void*)(uintptr_t)addr) ? 0 : -1;
    }
    if (info.Type == MEM_PRIVATE) {
        return VirtualFree((void*)(uintptr_t)addr, 0, MEM_RELEASE) ? 0 : -1;
    }
    return -1;
}

#endif
