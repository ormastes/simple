/* Secure, descriptor-pinned read-only file views for compiler snapshots.
 *
 * This is the sole C owner of rt_file_view_* and rt_pinned_archive_*.
 * Paths are opened component-by-component beneath an already opened root.
 * A path may be root-relative or use the root's exact absolute prefix; dot
 * components, symlinks, and non-regular leaves fail closed. Public handles
 * index this TU's private table, not host file
 * descriptors, so a forged handle cannot close an unrelated descriptor.
 */
#include "runtime.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* native_all needs a Rust-visible ABI owner as well as the standalone C
 * owner. In that build only, compile these bodies under private names; the
 * Rust module exports the public rt_* names as zero-policy aliases. */
#if defined(SIMPLE_RUNTIME_FILE_VIEW_RUST_OWNER)
#define rt_file_view_open_beneath_no_follow_v1 spl_c_file_view_open_beneath_no_follow_v1
#define rt_file_view_mapping_supported_v1 spl_c_file_view_mapping_supported_v1
#define rt_file_view_map_copy_v1 spl_c_file_view_map_copy_v1
#define rt_file_view_pread_exact_v1 spl_c_file_view_pread_exact_v1
#define rt_file_view_prefetch_v1 spl_c_file_view_prefetch_v1
#define rt_file_view_device_v1 spl_c_file_view_device_v1
#define rt_file_view_inode_v1 spl_c_file_view_inode_v1
#define rt_file_view_size_v1 spl_c_file_view_size_v1
#define rt_file_view_close_v1 spl_c_file_view_close_v1
#define rt_pinned_archive_open_beneath_v1 spl_c_pinned_archive_open_beneath_v1
#define rt_pinned_archive_device_v1 spl_c_pinned_archive_device_v1
#define rt_pinned_archive_inode_v1 spl_c_pinned_archive_inode_v1
#define rt_pinned_archive_size_v1 spl_c_pinned_archive_size_v1
#define rt_pinned_archive_close_v1 spl_c_pinned_archive_close_v1
#endif

#define FILE_VIEW_CAPACITY 1024
#define FILE_VIEW_HANDLE_BASE INT64_C(0x4656000000000000)
#define FILE_VIEW_TAG_MASK INT64_C(0xFFFFFC0000000000)

static int copy_text_value(int64_t value, char **out) {
    const uint8_t *data = rt_string_data(value);
    int64_t len = rt_string_len(value);
    if (len < 0 || len > 32768 || (!data && len) ||
        (len && memchr(data, 0, (size_t)len))) return -1;
    char *copy = (char *)malloc((size_t)len + 1);
    if (!copy) return 0;
    if (len) memcpy(copy, data, (size_t)len);
    copy[len] = 0;
    *out = copy;
    return 1;
}

static int decode_file_view_handle(int64_t handle, uint32_t *out_slot, uint32_t *out_generation) {
    if ((handle & FILE_VIEW_TAG_MASK) != FILE_VIEW_HANDLE_BASE) return 0;
    uint32_t slot = (uint32_t)(handle & 1023);
    uint32_t generation = (uint32_t)((uint64_t)handle >> 10);
    if (slot >= FILE_VIEW_CAPACITY || !generation) return 0;
    *out_slot = slot;
    *out_generation = generation;
    return 1;
}

static int64_t encode_file_view_handle(uint32_t slot, uint32_t generation) {
    return FILE_VIEW_HANDLE_BASE | ((int64_t)generation << 10) | (int64_t)slot;
}

static int valid_read_bounds(uint64_t offset, uint64_t length) {
    return offset <= (uint64_t)INT64_MAX &&
        length <= (uint64_t)SIZE_MAX &&
        length <= (uint64_t)INT64_MAX &&
        offset <= UINT64_MAX - length &&
        offset + length <= (uint64_t)INT64_MAX;
}

static int64_t bytes_array(const uint8_t *bytes, uint64_t length) {
    if (length > INT64_MAX) return 3;
    /* A [u8] must use the packed array ABI. Tagged i64 slots turn each
     * bounded read into eight times as much live storage. */
    SplArray *array = rt_byte_array_new_len(length);
    if (!array) return 3;
    for (uint64_t i = 0; i < length; ++i) {
        if (!rt_array_set(array, (int64_t)i, (int64_t)bytes[i] << 3)) {
            rt_array_free(array);
            return 3;
        }
    }
    return (int64_t)(uintptr_t)array;
}

#ifdef _WIN32

#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#ifndef NOMINMAX
#define NOMINMAX
#endif
#if !defined(_WIN32_WINNT) || _WIN32_WINNT < 0x0600
#undef _WIN32_WINNT
#define _WIN32_WINNT 0x0600
#endif
#include <windows.h>

/* Minimal NT structures for relative no-follow opens without winternl.h
 * header collisions across MinGW and MSVC toolchains. */
typedef struct {
    USHORT Length;
    USHORT MaximumLength;
    PWSTR Buffer;
} FvUnicodeString;

typedef struct {
    ULONG Length;
    HANDLE RootDirectory;
    FvUnicodeString *ObjectName;
    ULONG Attributes;
    PVOID SecurityDescriptor;
    PVOID SecurityQualityOfService;
} FvObjectAttributes;

typedef struct {
    union {
        LONG Status;
        PVOID Pointer;
    } u;
    ULONG_PTR Information;
} FvIoStatusBlock;

typedef LONG (NTAPI *FvNtCreateFileFn)(
    PHANDLE FileHandle,
    ACCESS_MASK DesiredAccess,
    FvObjectAttributes *ObjectAttributes,
    FvIoStatusBlock *IoStatusBlock,
    PLARGE_INTEGER AllocationSize,
    ULONG FileAttributes,
    ULONG ShareAccess,
    ULONG CreateDisposition,
    ULONG CreateOptions,
    PVOID EaBuffer,
    ULONG EaLength);

#define FV_OBJ_CASE_INSENSITIVE 0x00000040UL
#define FV_FILE_OPEN 0x00000001UL
#define FV_FILE_DIRECTORY_FILE 0x00000001UL
#define FV_FILE_SYNCHRONOUS_IO_NONALERT 0x00000020UL
#define FV_FILE_NON_DIRECTORY_FILE 0x00000040UL
#define FV_FILE_OPEN_REPARSE_POINT 0x00200000UL

static HANDLE file_view_handles[FILE_VIEW_CAPACITY];
static uint8_t file_view_occupied[FILE_VIEW_CAPACITY];
static uint32_t file_view_generations[FILE_VIEW_CAPACITY];
static SRWLOCK file_view_lock = SRWLOCK_INIT;

static int is_sep(char c) { return c == '/' || c == '\\'; }
static int is_ascii_alpha(char c) { return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'); }
static char ascii_lower(char c) { return (c >= 'A' && c <= 'Z') ? (char)(c + ('a' - 'A')) : c; }

static int has_drive_prefix(const char *s) {
    return s && is_ascii_alpha(s[0]) && s[1] == ':';
}

static int relative_path_valid(const char *path) {
    if (!path || !path[0] || is_sep(path[0])) return 0;
    const char *start = path;
    for (const char *p = path;; ++p) {
        unsigned char uc = (unsigned char)*p;
        if (uc != 0 && uc < 32) return 0;
        if (*p == ':') return 0;
        if (*p != '/' && *p != '\\' && *p != 0) continue;
        size_t n = (size_t)(p - start);
        if (n == 0 || (n == 1 && start[0] == '.') ||
            (n == 2 && start[0] == '.' && start[1] == '.')) return 0;
        if (*p == 0) return 1;
        start = p + 1;
    }
}

static int root_prefix_matches(const char *root, const char *path, size_t root_len) {
    if (ascii_lower(root[0]) != ascii_lower(path[0]) || path[1] != ':' || !is_sep(path[2]))
        return 0;
    for (size_t i = 3; i < root_len; ++i) {
        if (is_sep(root[i]) && is_sep(path[i])) continue;
        if (root[i] != path[i]) return 0;
    }
    return 1;
}

static const char *path_beneath_root(const char *root, const char *path) {
    size_t root_len = root ? strlen(root) : 0;
    if (!root_len || !path || !path[0]) return NULL;
    if (is_sep(root[0]) && is_sep(root[1])) return NULL;
    if (is_sep(path[0]) && is_sep(path[1])) return NULL;
    for (size_t i = 0; i < root_len; ++i) {
        if ((unsigned char)root[i] < 32) return NULL;
        if (root[i] == ':' && !(i == 1 && is_ascii_alpha(root[0]))) return NULL;
    }
    int root_drive = has_drive_prefix(root);
    if (root_drive) {
        if (!is_sep(root[2])) return NULL;
        if (root_len > 3 && is_sep(root[root_len - 1])) return NULL;
    } else {
        if (root_len > 1 && is_sep(root[root_len - 1])) return NULL;
    }
    if (has_drive_prefix(path)) {
        if (!is_sep(path[2]) || !root_drive) return NULL;
        size_t path_len = strlen(path);
        if (root_len == 3) return root_prefix_matches(root, path, 3) ? path + 3 : NULL;
        if (path_len <= root_len || !root_prefix_matches(root, path, root_len) ||
            !is_sep(path[root_len])) return NULL;
        return path + root_len + 1;
    }
    if (is_sep(path[0])) {
        if (root_len == 1 && is_sep(root[0])) return path + 1;
        return NULL;
    }
    return path;
}

static int utf8_to_wide_alloc(const char *utf8, wchar_t **out, size_t *out_len) {
    if (!utf8 || !utf8[0]) return 0;
    int count = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, utf8, -1, NULL, 0);
    if (count <= 0) return 0;
    wchar_t *wide = (wchar_t *)malloc((size_t)count * sizeof(wchar_t));
    if (!wide) return -1;
    if (!MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, utf8, -1, wide, count)) {
        free(wide);
        return 0;
    }
    *out = wide;
    if (out_len) *out_len = (size_t)(count - 1);
    return 1;
}

static int map_win32_open_error(DWORD err) {
    if (err == ERROR_DIRECTORY || err == ERROR_CANT_ACCESS_FILE ||
        err == ERROR_REPARSE_TAG_INVALID || err == ERROR_INVALID_REPARSE_DATA) return -3;
    return -1;
}

static int map_nt_open_error(uint32_t status) {
    if (status == 0xC0000103u || /* STATUS_NOT_A_DIRECTORY */
        status == 0xC00000BAu || /* STATUS_FILE_IS_A_DIRECTORY */
        status == 0x8000002Du || /* STATUS_STOPPED_ON_SYMLINK */
        status == 0xC0000275u || /* STATUS_IO_REPARSE_DATA_INVALID */
        status == 0xC0000277u || /* STATUS_IO_REPARSE_TAG_NOT_HANDLED */
        status == 0xC0000278u || /* STATUS_IO_REPARSE_TAG_MISMATCH */
        status == 0xC0000279u || /* STATUS_IO_REPARSE_TAG_INVALID */
        status == 0xC000050Bu)   /* STATUS_REPARSE_POINT_ENCOUNTERED */
        return -3;
    return -1;
}

static int verify_opened_kind(HANDLE h, int expect_dir, BY_HANDLE_FILE_INFORMATION *out_info) {
    if (GetFileType(h) != FILE_TYPE_DISK) return 0;
    BY_HANDLE_FILE_INFORMATION bhfi;
    if (!GetFileInformationByHandle(h, &bhfi)) return 0;
    if ((bhfi.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT) != 0) return 0;
    if (!!(bhfi.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) != !!expect_dir) return 0;
    FILE_ATTRIBUTE_TAG_INFO tag_info;
    if (!GetFileInformationByHandleEx(h, FileAttributeTagInfo, &tag_info, sizeof(tag_info)))
        return 0;
    if ((tag_info.FileAttributes & FILE_ATTRIBUTE_REPARSE_POINT) != 0) return 0;
    if (!!(tag_info.FileAttributes & FILE_ATTRIBUTE_DIRECTORY) != !!expect_dir) return 0;
    if (!expect_dir) {
        uint64_t size = ((uint64_t)bhfi.nFileSizeHigh << 32) | (uint64_t)bhfi.nFileSizeLow;
        if (size > (uint64_t)INT64_MAX) return 0;
    }
    if (out_info) *out_info = bhfi;
    return 1;
}

static int open_root_directory(const char *root, HANDLE *out_handle) {
    wchar_t *wide = NULL;
    size_t wlen = 0;
    int conv = utf8_to_wide_alloc(root, &wide, &wlen);
    if (conv <= 0) return conv == 0 ? -2 : -1;
    for (size_t i = 0; i < wlen; ++i) {
        if (wide[i] == L'/') wide[i] = L'\\';
    }
    wchar_t *open_path = wide;
    wchar_t *extended = NULL;
    if (wlen >= 248 && ((wide[0] >= L'A' && wide[0] <= L'Z') || (wide[0] >= L'a' && wide[0] <= L'z')) &&
        wide[1] == L':' && wide[2] == L'\\') {
        extended = (wchar_t *)malloc((wlen + 5) * sizeof(wchar_t));
        if (!extended) { free(wide); return -1; }
        extended[0] = L'\\'; extended[1] = L'\\'; extended[2] = L'?'; extended[3] = L'\\';
        memcpy(extended + 4, wide, (wlen + 1) * sizeof(wchar_t));
        open_path = extended;
    }
    HANDLE h = CreateFileW(
        open_path,
        FILE_LIST_DIRECTORY | FILE_READ_ATTRIBUTES | SYNCHRONIZE,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL,
        OPEN_EXISTING,
        FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT,
        NULL);
    DWORD err = (h == INVALID_HANDLE_VALUE) ? GetLastError() : 0;
    free(extended);
    free(wide);
    if (h == INVALID_HANDLE_VALUE) return map_win32_open_error(err);
    if (!verify_opened_kind(h, 1, NULL)) {
        CloseHandle(h);
        return -3;
    }
    *out_handle = h;
    return 0;
}

static int open_child_component(FvNtCreateFileFn nt_create_file, HANDLE parent,
                                wchar_t *component, int is_leaf, HANDLE *out_handle) {
    size_t comp_len = wcslen(component);
    if (comp_len == 0 || comp_len > 32767) return -2;
    FvUnicodeString us;
    us.Length = (USHORT)(comp_len * sizeof(wchar_t));
    us.MaximumLength = us.Length;
    us.Buffer = component;
    FvObjectAttributes oa;
    memset(&oa, 0, sizeof(oa));
    oa.Length = (ULONG)sizeof(oa);
    oa.RootDirectory = parent;
    oa.ObjectName = &us;
    oa.Attributes = FV_OBJ_CASE_INSENSITIVE;
    FvIoStatusBlock iosb;
    memset(&iosb, 0, sizeof(iosb));
    ACCESS_MASK access = is_leaf
        ? (FILE_READ_DATA | FILE_READ_ATTRIBUTES | SYNCHRONIZE)
        : (FILE_LIST_DIRECTORY | FILE_READ_ATTRIBUTES | SYNCHRONIZE);
    ULONG options = FV_FILE_OPEN_REPARSE_POINT | FV_FILE_SYNCHRONOUS_IO_NONALERT |
        (is_leaf ? FV_FILE_NON_DIRECTORY_FILE : FV_FILE_DIRECTORY_FILE);
    HANDLE opened = NULL;
    LONG status = nt_create_file(
        &opened, access, &oa, &iosb, NULL, FILE_ATTRIBUTE_NORMAL,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        FV_FILE_OPEN, options, NULL, 0);
    if (status < 0) return map_nt_open_error((uint32_t)status);
    if (!opened || opened == INVALID_HANDLE_VALUE) return -1;
    if (!verify_opened_kind(opened, !is_leaf, NULL)) {
        CloseHandle(opened);
        return -3;
    }
    *out_handle = opened;
    return 0;
}

static int open_regular_beneath(const char *root, const char *relative, HANDLE *out_handle) {
    if (!relative_path_valid(relative)) return -2;
    HMODULE ntdll = GetModuleHandleW(L"ntdll.dll");
    FvNtCreateFileFn nt_create_file = ntdll
        ? (FvNtCreateFileFn)(void *)GetProcAddress(ntdll, "NtCreateFile")
        : NULL;
    if (!nt_create_file) return -1;
    wchar_t *rel_w = NULL;
    size_t rel_wlen = 0;
    int conv = utf8_to_wide_alloc(relative, &rel_w, &rel_wlen);
    if (conv <= 0) return conv == 0 ? -2 : -1;
    HANDLE current = INVALID_HANDLE_VALUE;
    int rc = open_root_directory(root, &current);
    if (rc < 0) { free(rel_w); return rc; }
    wchar_t *part = rel_w;
    while (part && *part) {
        wchar_t *sep = part;
        while (*sep && *sep != L'/' && *sep != L'\\') ++sep;
        wchar_t *next = NULL;
        if (*sep) { *sep = 0; next = sep + 1; }
        HANDLE opened = INVALID_HANDLE_VALUE;
        rc = open_child_component(nt_create_file, current, part, next == NULL, &opened);
        CloseHandle(current);
        if (rc < 0) { free(rel_w); return rc; }
        current = opened;
        part = next;
    }
    free(rel_w);
    *out_handle = current;
    return 0;
}

static int64_t register_handle(HANDLE h) {
    int64_t result = -1;
    AcquireSRWLockExclusive(&file_view_lock);
    for (uint32_t i = 0; i < FILE_VIEW_CAPACITY; ++i) {
        if (!file_view_occupied[i]) {
            file_view_occupied[i] = 1;
            file_view_handles[i] = h;
            uint32_t generation = ++file_view_generations[i];
            if (!generation) generation = ++file_view_generations[i];
            result = encode_file_view_handle(i, generation);
            break;
        }
    }
    ReleaseSRWLockExclusive(&file_view_lock);
    if (result < 0) CloseHandle(h);
    return result;
}

static int lookup_slot_locked(int64_t handle, HANDLE *out_handle) {
    uint32_t slot = 0, generation = 0;
    if (!decode_file_view_handle(handle, &slot, &generation)) return -1;
    if (!file_view_occupied[slot] || file_view_generations[slot] != generation) return -1;
    if (out_handle) *out_handle = file_view_handles[slot];
    return (int)slot;
}

int64_t rt_file_view_open_beneath_no_follow_v1(int64_t root_value, int64_t path_value) {
    char *root = NULL, *path = NULL;
    int root_copy = copy_text_value(root_value, &root);
    if (root_copy <= 0) return root_copy < 0 ? -2 : -1;
    int path_copy = copy_text_value(path_value, &path);
    if (path_copy <= 0) {
        free(root);
        return path_copy < 0 ? -2 : -1;
    }
    const char *relative = path_beneath_root(root, path);
    HANDLE h = INVALID_HANDLE_VALUE;
    int rc = relative ? open_regular_beneath(root, relative, &h) : -2;
    free(root);
    free(path);
    return rc < 0 ? (int64_t)rc : register_handle(h);
}

int8_t rt_file_view_mapping_supported_v1(int64_t handle) {
    AcquireSRWLockExclusive(&file_view_lock);
    HANDLE h = INVALID_HANDLE_VALUE;
    int ok = lookup_slot_locked(handle, &h) >= 0 && verify_opened_kind(h, 0, NULL);
    ReleaseSRWLockExclusive(&file_view_lock);
    return (int8_t)ok;
}

static int read_mapped_win32(HANDLE h, uint64_t offset, uint64_t length, uint8_t *buffer) {
    SYSTEM_INFO sys_info;
    GetSystemInfo(&sys_info);
    uint64_t gran = sys_info.dwAllocationGranularity
        ? (uint64_t)sys_info.dwAllocationGranularity : UINT64_C(65536);
    uint64_t base = offset - (offset % gran);
    uint64_t delta = offset - base;
    if (length > (uint64_t)SIZE_MAX - delta) return 0;
    HANDLE mapping = CreateFileMappingW(h, NULL, PAGE_READONLY, 0, 0, NULL);
    if (!mapping) return 0;
    void *view = MapViewOfFile(
        mapping, FILE_MAP_READ, (DWORD)(base >> 32),
        (DWORD)(base & 0xFFFFFFFFu), (SIZE_T)(length + delta));
    int ok = view != NULL;
    if (ok) {
        memcpy(buffer, (const uint8_t *)view + delta, (size_t)length);
        UnmapViewOfFile(view);
    }
    CloseHandle(mapping);
    return ok;
}

static int read_pread_win32(HANDLE h, uint64_t offset, uint64_t length, uint8_t *buffer) {
    uint64_t done = 0;
    while (done < length) {
        uint64_t cur = offset + done;
        uint64_t rem = length - done;
        DWORD chunk = rem > UINT64_C(0x40000000) ? (DWORD)0x40000000u : (DWORD)rem;
        OVERLAPPED ov;
        memset(&ov, 0, sizeof(ov));
        ov.Offset = (DWORD)(cur & 0xFFFFFFFFu);
        ov.OffsetHigh = (DWORD)(cur >> 32);
        DWORD nread = 0;
        if (!ReadFile(h, buffer + done, chunk, &nread, &ov) || nread == 0) return 0;
        done += (uint64_t)nread;
    }
    return 1;
}

static int64_t read_exact_array(int64_t handle, uint64_t offset, uint64_t length, int mapped) {
    if (!valid_read_bounds(offset, length)) return 3;
    AcquireSRWLockExclusive(&file_view_lock);
    HANDLE h = INVALID_HANDLE_VALUE;
    BY_HANDLE_FILE_INFORMATION info;
    if (lookup_slot_locked(handle, &h) < 0 || !verify_opened_kind(h, 0, &info)) {
        ReleaseSRWLockExclusive(&file_view_lock);
        return 3;
    }
    uint64_t file_size = ((uint64_t)info.nFileSizeHigh << 32) | (uint64_t)info.nFileSizeLow;
    if (offset + length > file_size) {
        ReleaseSRWLockExclusive(&file_view_lock);
        return 3;
    }
    if (length == 0) {
        ReleaseSRWLockExclusive(&file_view_lock);
        return bytes_array(NULL, 0);
    }
    uint8_t *buffer = (uint8_t *)malloc((size_t)length);
    if (!buffer) {
        ReleaseSRWLockExclusive(&file_view_lock);
        return 3;
    }
    int ok = mapped
        ? read_mapped_win32(h, offset, length, buffer)
        : read_pread_win32(h, offset, length, buffer);
    ReleaseSRWLockExclusive(&file_view_lock);
    int64_t result = ok ? bytes_array(buffer, length) : 3;
    free(buffer);
    return result;
}

int8_t rt_file_view_prefetch_v1(int64_t handle, uint64_t offset, uint64_t length) {
    if (!valid_read_bounds(offset, length)) return 0;
    AcquireSRWLockExclusive(&file_view_lock);
    HANDLE h = INVALID_HANDLE_VALUE;
    BY_HANDLE_FILE_INFORMATION info;
    int valid = lookup_slot_locked(handle, &h) >= 0 && verify_opened_kind(h, 0, &info);
    if (valid) {
        uint64_t file_size = ((uint64_t)info.nFileSizeHigh << 32) | (uint64_t)info.nFileSizeLow;
        valid = offset + length <= file_size;
    }
    ReleaseSRWLockExclusive(&file_view_lock);
    return (int8_t)valid;
}

static int64_t identity_field(int64_t handle, int field) {
    AcquireSRWLockExclusive(&file_view_lock);
    HANDLE h = INVALID_HANDLE_VALUE;
    BY_HANDLE_FILE_INFORMATION info;
    int ok = lookup_slot_locked(handle, &h) >= 0 && verify_opened_kind(h, 0, &info);
    int64_t value = -1;
    if (ok) {
        if (field == 0) value = (int64_t)(uint64_t)info.dwVolumeSerialNumber;
        else if (field == 1) value = (int64_t)(((uint64_t)info.nFileIndexHigh << 32) | (uint64_t)info.nFileIndexLow);
        else value = (int64_t)(((uint64_t)info.nFileSizeHigh << 32) | (uint64_t)info.nFileSizeLow);
    }
    ReleaseSRWLockExclusive(&file_view_lock);
    return value;
}

int8_t rt_file_view_close_v1(int64_t handle) {
    AcquireSRWLockExclusive(&file_view_lock);
    HANDLE h = INVALID_HANDLE_VALUE;
    int slot = lookup_slot_locked(handle, &h);
    if (slot < 0) {
        ReleaseSRWLockExclusive(&file_view_lock);
        return 0;
    }
    file_view_occupied[slot] = 0;
    file_view_handles[slot] = INVALID_HANDLE_VALUE;
    ReleaseSRWLockExclusive(&file_view_lock);
    return (int8_t)(CloseHandle(h) != 0);
}

#else

#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#ifndef O_CLOEXEC
#define O_CLOEXEC 0
#endif
#ifndef O_NOFOLLOW
#define O_NOFOLLOW 0
#endif

static int file_view_fds[FILE_VIEW_CAPACITY];
static uint32_t file_view_generations[FILE_VIEW_CAPACITY];
static pthread_mutex_t file_view_lock = PTHREAD_MUTEX_INITIALIZER;

static int relative_path_valid(const char *path) {
    if (!path || !path[0] || path[0] == '/') return 0;
    const char *start = path;
    for (const char *p = path;; ++p) {
        if (*p != '/' && *p != 0) continue;
        size_t n = (size_t)(p - start);
        if (n == 0 || (n == 1 && start[0] == '.') ||
            (n == 2 && start[0] == '.' && start[1] == '.')) return 0;
        if (*p == 0) return 1;
        start = p + 1;
    }
}

static const char *path_beneath_root(const char *root, const char *path) {
    size_t root_len = root ? strlen(root) : 0;
    if (!root_len || (root_len > 1 && root[root_len - 1] == '/')) return NULL;
    if (!path || path[0] != '/') return path;
    if (root[0] != '/') return NULL;
    if (root_len == 1) return path + 1;
    if (strncmp(root, path, root_len) != 0 || path[root_len] != '/') return NULL;
    return path + root_len + 1;
}

static int open_regular_beneath(const char *root, const char *relative) {
    if (!relative_path_valid(relative)) return -2;
    int current = open(root, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (current < 0) return (errno == ELOOP || errno == ENOTDIR ? -3 : -1);
    char *work = strdup(relative);
    if (!work) { close(current); return -1; }
    char *save = NULL;
    char *part = strtok_r(work, "/", &save);
    while (part) {
        char *next = strtok_r(NULL, "/", &save);
        /* A child-created FIFO must not block before fstat rejects it. */
        int flags = O_RDONLY | O_NOFOLLOW | O_CLOEXEC |
            (next ? O_DIRECTORY : O_NONBLOCK);
        int opened = openat(current, part, flags);
        int saved_errno = errno;
        close(current);
        if (opened < 0) {
            free(work);
            return (saved_errno == ELOOP || saved_errno == ENOTDIR ? -3 : -1);
        }
        current = opened;
        part = next;
    }
    free(work);
    struct stat st;
    if (fstat(current, &st) != 0 || !S_ISREG(st.st_mode)) {
        close(current);
        return -3;
    }
    return current;
}

static int64_t register_fd(int fd) {
    int64_t result = -1;
    pthread_mutex_lock(&file_view_lock);
    for (uint32_t i = 0; i < FILE_VIEW_CAPACITY; ++i) {
        if (file_view_fds[i] == 0) {
            file_view_fds[i] = fd + 1;
            uint32_t generation = ++file_view_generations[i];
            if (!generation) generation = ++file_view_generations[i];
            result = encode_file_view_handle(i, generation);
            break;
        }
    }
    pthread_mutex_unlock(&file_view_lock);
    if (result < 0) close(fd);
    return result;
}

static int lookup_fd_locked(int64_t handle) {
    uint32_t slot = 0, generation = 0;
    if (!decode_file_view_handle(handle, &slot, &generation)) return -1;
    if (file_view_fds[slot] == 0 || file_view_generations[slot] != generation) return -1;
    return file_view_fds[slot] - 1;
}

int64_t rt_file_view_open_beneath_no_follow_v1(int64_t root_value, int64_t path_value) {
    char *root = NULL, *path = NULL;
    int root_copy = copy_text_value(root_value, &root);
    if (root_copy <= 0) return root_copy < 0 ? -2 : -1;
    int path_copy = copy_text_value(path_value, &path);
    if (path_copy <= 0) {
        free(root);
        return path_copy < 0 ? -2 : -1;
    }
    const char *relative = path_beneath_root(root, path);
    int fd = relative ? open_regular_beneath(root, relative) : -2;
    free(root); free(path);
    return fd < 0 ? fd : register_fd(fd);
}

int8_t rt_file_view_mapping_supported_v1(int64_t handle) {
    pthread_mutex_lock(&file_view_lock);
    int ok = lookup_fd_locked(handle) >= 0;
    pthread_mutex_unlock(&file_view_lock);
    return (int8_t)ok;
}

static int64_t read_exact_array(int64_t handle, uint64_t offset, uint64_t length, int mapped) {
    if (!valid_read_bounds(offset, length)) return 3;
    pthread_mutex_lock(&file_view_lock);
    int fd = lookup_fd_locked(handle);
    if (fd < 0) { pthread_mutex_unlock(&file_view_lock); return 3; }
    struct stat st;
    if (fstat(fd, &st) != 0 || st.st_size < 0 ||
        offset + length > (uint64_t)st.st_size) {
        pthread_mutex_unlock(&file_view_lock);
        return 3;
    }
    uint8_t *buffer = length ? (uint8_t *)malloc((size_t)length) : NULL;
    if (length && !buffer) { pthread_mutex_unlock(&file_view_lock); return 3; }
    int ok = 1;
    if (mapped && length) {
        long page = sysconf(_SC_PAGESIZE);
        if (page <= 0) page = 4096;
        uint64_t base = offset - (offset % (uint64_t)page);
        uint64_t delta = offset - base;
        if (length > SIZE_MAX - delta) ok = 0;
        void *map = ok ? mmap(NULL, (size_t)(length + delta), PROT_READ, MAP_PRIVATE, fd, (off_t)base) : MAP_FAILED;
        if (map == MAP_FAILED) ok = 0;
        else { memcpy(buffer, (uint8_t *)map + delta, (size_t)length); munmap(map, (size_t)(length + delta)); }
    } else {
        uint64_t done = 0;
        while (done < length) {
            ssize_t n = pread(fd, buffer + done, (size_t)(length - done), (off_t)(offset + done));
            if (n < 0 && errno == EINTR) continue;
            if (n <= 0) { ok = 0; break; }
            done += (uint64_t)n;
        }
    }
    int64_t result = ok ? bytes_array(buffer, length) : 3;
    free(buffer);
    pthread_mutex_unlock(&file_view_lock);
    return result;
}

int8_t rt_file_view_prefetch_v1(int64_t handle, uint64_t offset, uint64_t length) {
    if (!valid_read_bounds(offset, length)) return 0;
    pthread_mutex_lock(&file_view_lock);
    int fd = lookup_fd_locked(handle);
    struct stat st;
    int valid = fd >= 0 && fstat(fd, &st) == 0 && st.st_size >= 0 &&
        offset + length <= (uint64_t)st.st_size;
#if defined(POSIX_FADV_WILLNEED)
    int ok = valid && posix_fadvise(fd, (off_t)offset, (off_t)length, POSIX_FADV_WILLNEED) == 0;
#else
    int ok = valid; (void)offset; (void)length;
#endif
    pthread_mutex_unlock(&file_view_lock);
    return (int8_t)ok;
}

static int64_t identity_field(int64_t handle, int field) {
    pthread_mutex_lock(&file_view_lock);
    int fd = lookup_fd_locked(handle);
    struct stat st;
    int ok = fd >= 0 && fstat(fd, &st) == 0 && S_ISREG(st.st_mode);
    int64_t value = -1;
    if (ok) value = field == 0 ? (int64_t)st.st_dev : field == 1 ? (int64_t)st.st_ino : (int64_t)st.st_size;
    pthread_mutex_unlock(&file_view_lock);
    return value;
}

int8_t rt_file_view_close_v1(int64_t handle) {
    pthread_mutex_lock(&file_view_lock);
    int fd = lookup_fd_locked(handle);
    if (fd < 0) { pthread_mutex_unlock(&file_view_lock); return 0; }
    uint32_t slot = (uint32_t)(handle & 1023);
    file_view_fds[slot] = 0;
    pthread_mutex_unlock(&file_view_lock);
    return (int8_t)(close(fd) == 0);
}

#endif

int64_t rt_file_view_map_copy_v1(int64_t handle, uint64_t offset, uint64_t length) { return read_exact_array(handle, offset, length, 1); }
int64_t rt_file_view_pread_exact_v1(int64_t handle, uint64_t offset, uint64_t length) { return read_exact_array(handle, offset, length, 0); }
int64_t rt_file_view_device_v1(int64_t handle) { return identity_field(handle, 0); }
int64_t rt_file_view_inode_v1(int64_t handle) { return identity_field(handle, 1); }
int64_t rt_file_view_size_v1(int64_t handle) { return identity_field(handle, 2); }

int64_t rt_pinned_archive_open_beneath_v1(int64_t root, int64_t path) { return rt_file_view_open_beneath_no_follow_v1(root, path); }
int64_t rt_pinned_archive_device_v1(int64_t handle) { return rt_file_view_device_v1(handle); }
int64_t rt_pinned_archive_inode_v1(int64_t handle) { return rt_file_view_inode_v1(handle); }
int64_t rt_pinned_archive_size_v1(int64_t handle) { return rt_file_view_size_v1(handle); }
int8_t rt_pinned_archive_close_v1(int64_t handle) { return rt_file_view_close_v1(handle); }
