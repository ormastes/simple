/* Windows implementations of the M3 exclusive, no-follow copy and hard-link
 * primitives (rt_file_copy_create_excl_no_follow /
 * rt_file_link_create_excl_no_follow). Shared by runtime.c and
 * runtime_native.c; mirrors the POSIX O_EXCL|O_NOFOLLOW and link()+inode
 * recheck semantics:
 *   - the source is opened with FILE_FLAG_OPEN_REPARSE_POINT and must be a
 *     regular file (no reparse point, no directory);
 *   - the copy destination is created with CREATE_NEW (an existing name of any
 *     kind, including a symlink, is refused, and the reparse flag stops a
 *     dangling link being followed);
 *   - the link is made with CreateHardLinkW (refuses an existing name) and then
 *     re-opened no-follow and must share the source's volume serial + file id,
 *     otherwise it is removed.
 * Inputs are UTF-8 paths already length-checked by the caller. */
#ifndef RT_WIN_EXCL_FILE_H
#define RT_WIN_EXCL_FILE_H

#if defined(_WIN32)
#include <windows.h>
#include "runtime_win_long_path.h"

static inline HANDLE rt_win_excl_open_regular_no_follow(
        const wchar_t* wide, BY_HANDLE_FILE_INFORMATION* info) {
    HANDLE h = CreateFileW(wide, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, NULL,
        OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL | FILE_FLAG_OPEN_REPARSE_POINT,
        NULL);
    if (h == INVALID_HANDLE_VALUE) return INVALID_HANDLE_VALUE;
    if (!GetFileInformationByHandle(h, info) ||
            (info->dwFileAttributes &
                (FILE_ATTRIBUTE_REPARSE_POINT | FILE_ATTRIBUTE_DIRECTORY))) {
        CloseHandle(h);
        return INVALID_HANDLE_VALUE;
    }
    return h;
}

static inline int rt_win_file_copy_create_excl_no_follow(
        const char* source, const char* destination) {
    wchar_t* wsrc = rt_win_long_path_widen(source);
    wchar_t* wdst = rt_win_long_path_widen(destination);
    int ok = 0;
    HANDLE in = INVALID_HANDLE_VALUE;
    HANDLE out = INVALID_HANDLE_VALUE;
    if (!wsrc || !wdst) goto done;
    BY_HANDLE_FILE_INFORMATION info;
    in = rt_win_excl_open_regular_no_follow(wsrc, &info);
    if (in == INVALID_HANDLE_VALUE) goto done;
    out = CreateFileW(wdst, GENERIC_WRITE, 0, NULL, CREATE_NEW,
        FILE_ATTRIBUTE_NORMAL | FILE_FLAG_OPEN_REPARSE_POINT, NULL);
    if (out == INVALID_HANDLE_VALUE) goto done;
    {
        unsigned char buffer[65536];
        ok = 1;
        for (;;) {
            DWORD count = 0;
            if (!ReadFile(in, buffer, (DWORD)sizeof(buffer), &count, NULL)) {
                ok = 0; break;
            }
            if (count == 0) break;
            DWORD offset = 0;
            while (offset < count) {
                DWORD written = 0;
                if (!WriteFile(out, buffer + offset, count - offset, &written,
                        NULL) || written == 0) { ok = 0; break; }
                offset += written;
            }
            if (!ok) break;
        }
        if (ok && !FlushFileBuffers(out)) ok = 0;
        if (!CloseHandle(out)) ok = 0;
        out = INVALID_HANDLE_VALUE;
        if (!ok) DeleteFileW(wdst);
    }
done:
    if (in != INVALID_HANDLE_VALUE) CloseHandle(in);
    free(wsrc);
    free(wdst);
    return ok;
}

static inline int rt_win_file_link_create_excl_no_follow(
        const char* source, const char* destination) {
    wchar_t* wsrc = rt_win_long_path_widen(source);
    wchar_t* wdst = rt_win_long_path_widen(destination);
    int ok = 0;
    HANDLE in = INVALID_HANDLE_VALUE;
    if (!wsrc || !wdst) goto done;
    BY_HANDLE_FILE_INFORMATION src_info;
    in = rt_win_excl_open_regular_no_follow(wsrc, &src_info);
    if (in == INVALID_HANDLE_VALUE) goto done;
    if (!CreateHardLinkW(wdst, wsrc, NULL)) goto done;
    {
        BY_HANDLE_FILE_INFORMATION dst_info;
        HANDLE check = rt_win_excl_open_regular_no_follow(wdst, &dst_info);
        if (check != INVALID_HANDLE_VALUE) CloseHandle(check);
        ok = check != INVALID_HANDLE_VALUE &&
            dst_info.dwVolumeSerialNumber == src_info.dwVolumeSerialNumber &&
            dst_info.nFileIndexHigh == src_info.nFileIndexHigh &&
            dst_info.nFileIndexLow == src_info.nFileIndexLow;
        if (!ok) DeleteFileW(wdst);
    }
done:
    if (in != INVALID_HANDLE_VALUE) CloseHandle(in);
    free(wsrc);
    free(wdst);
    return ok;
}
#endif /* _WIN32 */
#endif /* RT_WIN_EXCL_FILE_H */
