/* codex-impl: single hosted-C owner for the portable host-file ABI. */
#if !defined(SIMPLE_RUNTIME_HOST_FILE_EXPORTS_OWNER_V2)
#error "runtime_host_file_exports.c must be instantiated only by runtime_native.c"
#endif
#if defined(SIMPLE_RUNTIME_FREESTANDING_V2)
#error "host-file exports cannot be instantiated in a freestanding profile"
#endif
#if !(defined(__linux__) || defined(__APPLE__) || defined(_WIN32))
#error "runtime host-file exports have no admitted provider for this target"
#endif

#include "runtime.h"

#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#include <windows.h>
#else
#include <errno.h>
#include <fcntl.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>
#endif

#define RT_HOST_FILE_PATH_MAX 4096U

static char* rt_host_file_copy_path(const uint8_t* path_ptr, uint64_t path_len) {
    if (!path_ptr || path_len == 0 || path_len >= RT_HOST_FILE_PATH_MAX ||
        path_len > (uint64_t)(SIZE_MAX - 1U)) {
        return NULL;
    }
    if (memchr(path_ptr, 0, (size_t)path_len) != NULL) return NULL;
    char* path = (char*)malloc((size_t)path_len + 1U);
    if (!path) return NULL;
    memcpy(path, path_ptr, (size_t)path_len);
    path[path_len] = 0;
    return path;
}

static char* rt_host_file_copy_tagged_path(int64_t path_value) {
    int64_t path_len = rt_string_len(path_value);
    const uint8_t* path_ptr = rt_string_data(path_value);
    if (path_len <= 0) return NULL;
    return rt_host_file_copy_path(path_ptr, (uint64_t)path_len);
}

static int64_t rt_host_file_owned_bytes(const uint8_t* bytes, uint64_t length) {
    if (length > (uint64_t)INT64_MAX) return 0;
    SplArray* array = rt_byte_array_new_len(length);
    if (!array) return 0;
    int64_t value = (int64_t)(uintptr_t)array;
    if (rt_array_bytes_store_checked(value, bytes, (int64_t)length) != (int64_t)length) {
        rt_array_free(array);
        return 0;
    }
    return value;
}

int rt_file_fsync(const uint8_t* path_ptr, uint64_t path_len) {
    char* path = rt_host_file_copy_path(path_ptr, path_len);
    if (!path) return 0;
#if defined(_WIN32)
    HANDLE file = CreateFileA(path, GENERIC_READ | GENERIC_WRITE,
                              FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
                              NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    free(path);
    if (file == INVALID_HANDLE_VALUE) return 0;
    int ok = FlushFileBuffers(file) != 0;
    if (!CloseHandle(file)) ok = 0;
    return ok ? 1 : 0;
#else
    int fd = open(path, O_RDONLY);
    free(path);
    if (fd < 0) return 0;
#if defined(__APPLE__) && defined(F_FULLFSYNC)
    int ok = fcntl(fd, F_FULLFSYNC) == 0;
#else
    int ok = fsync(fd) == 0;
#endif
    if (close(fd) != 0) ok = 0;
    return ok ? 1 : 0;
#endif
}

int64_t rt_file_lock(const uint8_t* path_ptr, uint64_t path_len, int64_t timeout_secs) {
    char* path = rt_host_file_copy_path(path_ptr, path_len);
    if (!path) return -1;
#if defined(_WIN32)
    HANDLE file = CreateFileA(path, GENERIC_READ | GENERIC_WRITE,
                              FILE_SHARE_READ | FILE_SHARE_WRITE,
                              NULL, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    free(path);
    if (file == INVALID_HANDLE_VALUE) return -1;
    OVERLAPPED overlapped;
    memset(&overlapped, 0, sizeof(overlapped));
    DWORD flags = LOCKFILE_EXCLUSIVE_LOCK;
    if (timeout_secs <= 0) {
        if (!LockFileEx(file, flags, 0, MAXDWORD, MAXDWORD, &overlapped)) {
            CloseHandle(file);
            return -1;
        }
        return (int64_t)(intptr_t)file;
    }
    flags |= LOCKFILE_FAIL_IMMEDIATELY;
    ULONGLONG timeout_ms = (uint64_t)timeout_secs > (UINT64_MAX / 1000U)
        ? UINT64_MAX : (ULONGLONG)timeout_secs * 1000U;
    ULONGLONG start = GetTickCount64();
    for (;;) {
        if (LockFileEx(file, flags, 0, MAXDWORD, MAXDWORD, &overlapped)) {
            return (int64_t)(intptr_t)file;
        }
        if (GetTickCount64() - start >= timeout_ms) break;
        Sleep(50);
    }
    CloseHandle(file);
    return -1;
#else
    int fd = open(path, O_RDWR | O_CREAT, 0644);
    free(path);
    if (fd < 0) return -1;
    if (timeout_secs <= 0) {
        if (flock(fd, LOCK_EX) == 0) return fd;
        close(fd);
        return -1;
    }
    int64_t timeout_ms = timeout_secs > INT64_MAX / 1000 ? INT64_MAX : timeout_secs * 1000;
    const int64_t sleep_ms = 50;
    const struct timespec pause = {0, sleep_ms * 1000000L};
    int64_t waited_ms = 0;
    while (waited_ms <= timeout_ms) {
        if (flock(fd, LOCK_EX | LOCK_NB) == 0) return fd;
        if (errno != EWOULDBLOCK && errno != EAGAIN) break;
        if (waited_ms >= timeout_ms) break;
        nanosleep(&pause, NULL);
        waited_ms += sleep_ms;
    }
    close(fd);
    return -1;
#endif
}

bool rt_file_unlock(int64_t handle) {
#if defined(_WIN32)
    if (handle == 0 || handle == -1) return false;
    HANDLE file = (HANDLE)(intptr_t)handle;
    OVERLAPPED overlapped;
    memset(&overlapped, 0, sizeof(overlapped));
    int unlocked = UnlockFileEx(file, 0, MAXDWORD, MAXDWORD, &overlapped) != 0;
    int closed = CloseHandle(file) != 0;
    return unlocked && closed;
#else
    if (handle < 0 || handle > INT_MAX) return false;
    int fd = (int)handle;
    int unlocked = flock(fd, LOCK_UN) == 0;
    int closed = close(fd) == 0;
    return unlocked && closed;
#endif
}

int64_t rt_file_mmap_read_bytes(const uint8_t* path_ptr, uint64_t path_len) {
    char* path = rt_host_file_copy_path(path_ptr, path_len);
    if (!path) return 0;
#if defined(_WIN32)
    HANDLE file = CreateFileA(path, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
                              NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    free(path);
    if (file == INVALID_HANDLE_VALUE) return 0;
    LARGE_INTEGER file_size;
    if (!GetFileSizeEx(file, &file_size) || file_size.QuadPart < 0) {
        CloseHandle(file);
        return 0;
    }
    uint64_t length = (uint64_t)file_size.QuadPart;
    if (length > (uint64_t)INT64_MAX || length > (uint64_t)SIZE_MAX) {
        CloseHandle(file);
        return 0;
    }
    if (length == 0) {
        CloseHandle(file);
        return rt_host_file_owned_bytes(NULL, 0);
    }
    HANDLE mapping = CreateFileMappingA(file, NULL, PAGE_READONLY, 0, 0, NULL);
    CloseHandle(file);
    if (!mapping) return 0;
    const uint8_t* mapped = (const uint8_t*)MapViewOfFile(mapping, FILE_MAP_READ, 0, 0, (SIZE_T)length);
    CloseHandle(mapping);
    if (!mapped) return 0;
    int64_t result = rt_host_file_owned_bytes(mapped, length);
    if (!UnmapViewOfFile(mapped)) {
        if (result != 0) rt_array_free((SplArray*)(uintptr_t)result);
        return 0;
    }
    return result;
#else
    int fd = open(path, O_RDONLY);
    free(path);
    if (fd < 0) return 0;
    struct stat info;
    if (fstat(fd, &info) != 0 || info.st_size < 0) {
        close(fd);
        return 0;
    }
    uint64_t length = (uint64_t)info.st_size;
    if (length > (uint64_t)INT64_MAX || length > (uint64_t)SIZE_MAX) {
        close(fd);
        return 0;
    }
    if (length == 0) {
        close(fd);
        return rt_host_file_owned_bytes(NULL, 0);
    }
    const uint8_t* mapped = (const uint8_t*)mmap(NULL, (size_t)length, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
    if (mapped == MAP_FAILED) return 0;
    int64_t result = rt_host_file_owned_bytes(mapped, length);
    if (munmap((void*)mapped, (size_t)length) != 0) {
        if (result != 0) rt_array_free((SplArray*)(uintptr_t)result);
        return 0;
    }
    return result;
#endif
}

int64_t rt_mmap(int64_t path_value, int64_t size, int64_t offset, int64_t readonly) {
    if (size <= 0 || offset < 0) return 0;
    char* path = rt_host_file_copy_tagged_path(path_value);
    if (!path) return 0;
#if defined(_WIN32)
    DWORD access = readonly != 0 ? GENERIC_READ : (GENERIC_READ | GENERIC_WRITE);
    DWORD protect = readonly != 0 ? PAGE_READONLY : PAGE_READWRITE;
    DWORD map_access = readonly != 0 ? FILE_MAP_READ : FILE_MAP_WRITE;
    HANDLE file = CreateFileA(path, access, FILE_SHARE_READ | FILE_SHARE_WRITE,
                              NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    free(path);
    if (file == INVALID_HANDLE_VALUE) return 0;
    HANDLE mapping = CreateFileMappingA(file, NULL, protect, 0, 0, NULL);
    CloseHandle(file);
    if (!mapping) return 0;
    DWORD offset_high = (DWORD)(((uint64_t)offset) >> 32U);
    DWORD offset_low = (DWORD)((uint64_t)offset & 0xffffffffU);
    void* address = MapViewOfFile(mapping, map_access, offset_high, offset_low, (SIZE_T)size);
    CloseHandle(mapping);
    return (int64_t)(intptr_t)address;
#else
    int flags = readonly != 0 ? O_RDONLY : O_RDWR;
    int fd = open(path, flags);
    free(path);
    if (fd < 0) return 0;
    int protection = readonly != 0 ? PROT_READ : (PROT_READ | PROT_WRITE);
    void* address = mmap(NULL, (size_t)size, protection, MAP_SHARED, fd, (off_t)offset);
    close(fd);
    return address == MAP_FAILED ? 0 : (int64_t)(intptr_t)address;
#endif
}

bool rt_munmap(int64_t addr, int64_t size) {
    if (addr == 0 || size <= 0) return false;
#if defined(_WIN32)
    return UnmapViewOfFile((void*)(intptr_t)addr) != 0;
#else
    return munmap((void*)(intptr_t)addr, (size_t)size) == 0;
#endif
}

bool rt_madvise(int64_t addr, int64_t size, int64_t advice) {
    if (addr == 0 || size <= 0) return false;
#if defined(_WIN32)
    (void)advice;
    return false;
#else
    int native_advice;
    switch (advice) {
        case 0: native_advice = MADV_NORMAL; break;
        case 1: native_advice = MADV_RANDOM; break;
        case 2: native_advice = MADV_SEQUENTIAL; break;
        case 3: native_advice = MADV_WILLNEED; break;
        case 4: native_advice = MADV_DONTNEED; break;
        default: return false;
    }
    return madvise((void*)(intptr_t)addr, (size_t)size, native_advice) == 0;
#endif
}

bool rt_msync(int64_t addr, int64_t size) {
    if (addr == 0 || size <= 0) return false;
#if defined(_WIN32)
    return FlushViewOfFile((void*)(intptr_t)addr, (SIZE_T)size) != 0;
#else
    return msync((void*)(intptr_t)addr, (size_t)size, MS_SYNC) == 0;
#endif
}
