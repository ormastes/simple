/* runtime_file_fsync_impl.h -- private fsync worker shared by runtime.c and
 * runtime_native.c.
 *
 * Not a public header: include it exactly once, from one translation unit,
 * after <stdio.h> and, on _WIN32, after platform/runtime_win_long_path.h
 * (rt_widen_long_path_rc); on POSIX after <unistd.h>. Everything here is
 * static; the exported rt_file_fsync / rt_file_fsync_cached entry points stay
 * hand-written in each includer and convert the compiler's (ptr, len) `text`
 * pair into the NUL-terminated C string this worker takes. */
#ifndef SIMPLE_RUNTIME_FILE_FSYNC_IMPL_H
#define SIMPLE_RUNTIME_FILE_FSYNC_IMPL_H

static int rt_fsync_path(const char* path) {
    if (!path) return 0;
#if defined(_WIN32)
    /* fopen()+fflush() was doubly wrong on Windows: fopen() is an ANSI/
     * narrow-CRT entry point capped at MAX_PATH (260 chars) -- the same bug
     * class as rt_file_create_excl, and a bootstrap generation path
     * routinely exceeds it -- and fflush() only empties the CRT's userspace
     * buffer, it gives no OS-level durability guarantee at all. Use the wide,
     * extended-length-prefixed CreateFileW + FlushFileBuffers pair instead,
     * exactly like rt_file_create_excl's fix; fall back to the ANSI
     * CreateFileA + FlushFileBuffers pair only when the path cannot be
     * widened. GENERIC_WRITE is required for FlushFileBuffers to succeed
     * (Windows refuses it on a read-only handle with ERROR_ACCESS_DENIED).
     * FILE_FLAG_BACKUP_SEMANTICS is required too: callers durability-sync
     * DIRECTORIES through this same worker (native_noop_admission.spl syncs
     * "{root}/generations" after a rename, the POSIX fsync-the-parent-dir
     * idiom), and CreateFile refuses to open a directory handle at all
     * without that flag (ERROR_ACCESS_DENIED). It is harmless on a regular
     * file -- the flag only widens what CreateFile will open, it does not
     * change file semantics. */
    wchar_t* wide_path = rt_widen_long_path_rc(path);
    HANDLE file = INVALID_HANDLE_VALUE;
    if (wide_path) {
        file = CreateFileW(wide_path, GENERIC_READ | GENERIC_WRITE,
                           FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
                           NULL, OPEN_EXISTING,
                           FILE_ATTRIBUTE_NORMAL | FILE_FLAG_BACKUP_SEMANTICS, NULL);
        free(wide_path);
    } else {
        file = CreateFileA(path, GENERIC_READ | GENERIC_WRITE,
                           FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
                           NULL, OPEN_EXISTING,
                           FILE_ATTRIBUTE_NORMAL | FILE_FLAG_BACKUP_SEMANTICS, NULL);
    }
    if (file == INVALID_HANDLE_VALUE) return 0;
    int ok = FlushFileBuffers(file) != 0;
    if (!CloseHandle(file)) ok = 0;
    return ok ? 1 : 0;
#else
    FILE* file = fopen(path, "rb");
    if (!file) return 0;
    int ok = fsync(fileno(file)) == 0;
    fclose(file);
    return ok ? 1 : 0;
#endif
}

#endif /* SIMPLE_RUNTIME_FILE_FSYNC_IMPL_H */
