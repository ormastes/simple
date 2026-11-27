/* Windows owner-only atomic file provider shared by core C and Rust.
 * The protected owner/System DACL is attached by CREATE_NEW, before bytes
 * exist. chmod after publication cannot provide this privacy contract. */
#ifndef SIMPLE_RUNTIME_WINDOWS_PRIVATE_ATOMIC_H
#define SIMPLE_RUNTIME_WINDOWS_PRIVATE_ATOMIC_H
#if defined(_WIN32)
#include "runtime_win_long_path.h"
#include <errno.h>
#include <stdatomic.h>
#include <sys/stat.h>
#include <io.h>
#include <fcntl.h>

static inline int rt_win_private_atomic_write(const char *path,
        const unsigned char *content, size_t length, int mode) {
    static atomic_uint_fast64_t sequence = 0;
    if (!path || !*path || (!content && length) || (mode & 0077)) return 0;
    size_t capacity = strlen(path) + 64;
    char *temp = (char *)malloc(capacity);
    wchar_t *target = rt_win_long_path_widen(path);
    if (!temp || !target) { free(temp); free(target); return 0; }
    typedef BOOL (WINAPI *ConvertSddlFn)(const char *, DWORD, PSECURITY_DESCRIPTOR *, ULONG *);
    HMODULE advapi = LoadLibraryA("advapi32.dll");
    ConvertSddlFn convert = advapi ? (ConvertSddlFn)GetProcAddress(advapi,
        "ConvertStringSecurityDescriptorToSecurityDescriptorA") : NULL;
    PSECURITY_DESCRIPTOR descriptor = NULL;
    if (!convert || !convert("D:P(A;;FA;;;SY)(A;;FA;;;OW)", 1, &descriptor, NULL)) {
        if (advapi) FreeLibrary(advapi);
        free(temp); free(target);
        return 0;
    }
    SECURITY_ATTRIBUTES attributes = { sizeof(attributes), descriptor, FALSE };
    int fd = -1;
    wchar_t *wide = NULL;
    for (int attempt = 0; attempt < 16 && fd < 0; attempt++) {
        int n = snprintf(temp, capacity, "%s.tmp.%lu.%llu", path,
            (unsigned long)GetCurrentProcessId(),
            (unsigned long long)atomic_fetch_add(&sequence, 1));
        if (n < 0 || (size_t)n >= capacity) break;
        free(wide);
        wide = rt_win_long_path_widen(temp);
        if (!wide) break;
        HANDLE handle = CreateFileW(wide, GENERIC_WRITE, 0, &attributes,
            CREATE_NEW, FILE_ATTRIBUTE_NORMAL | FILE_FLAG_OPEN_REPARSE_POINT, NULL);
        if (handle == INVALID_HANDLE_VALUE) {
            DWORD error = GetLastError();
            errno = error == ERROR_FILE_EXISTS || error == ERROR_ALREADY_EXISTS ? EEXIST : EACCES;
        } else {
            fd = _open_osfhandle((intptr_t)handle, _O_WRONLY | _O_BINARY);
            if (fd < 0) {
                CloseHandle(handle);
                DeleteFileW(wide);
                break;
            }
        }
        if (fd < 0 && errno != EEXIST) break;
    }
    LocalFree(descriptor);
    FreeLibrary(advapi);
    int created = fd >= 0;
    FILE *file = fd < 0 ? NULL : _fdopen(fd, "wb");
    int ok = file != NULL;
    if (ok) ok = fwrite(content, 1, length, file) == length;
    if (ok) ok = fflush(file) == 0;
    if (ok) ok = _commit(fd) == 0;
    if (file && fclose(file) != 0) ok = 0;
    else if (!file && fd >= 0) _close(fd);
    /* Windows only maps the owner-write bit to its readonly attribute;
     * the DACL above independently enforces the owner-only reader set. */
    if (ok) ok = _wchmod(wide, _S_IREAD | ((mode & 0200) ? _S_IWRITE : 0)) == 0;
    if (ok) ok = MoveFileExW(wide, target,
        MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH) != 0;
    if (created && !ok) {
        _wchmod(wide, _S_IREAD | _S_IWRITE);
        DeleteFileW(wide);
    }
    free(wide); free(target); free(temp);
    return ok;
}
#endif
#endif
