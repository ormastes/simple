/* Shared core/full Windows cleanup: UTF-8, long descendants, no reparse walk. */
#ifndef SIMPLE_RUNTIME_WIN_REMOVE_TREE_H
#define SIMPLE_RUNTIME_WIN_REMOVE_TREE_H
#include <stdbool.h>
#include "runtime_win_long_path.h"

static bool rt_win_remove_tree_wide(const wchar_t* path, bool missing_ok) {
    DWORD attrs = GetFileAttributesW(path);
    if (attrs == INVALID_FILE_ATTRIBUTES) {
        DWORD error = GetLastError();
        return missing_ok && (error == ERROR_FILE_NOT_FOUND || error == ERROR_PATH_NOT_FOUND);
    }
    if (!(attrs & FILE_ATTRIBUTE_DIRECTORY)) return DeleteFileW(path) != 0;
    if (attrs & FILE_ATTRIBUTE_REPARSE_POINT) return RemoveDirectoryW(path) != 0;

    size_t length = wcslen(path);
    bool trailing_separator = length > 0 && path[length - 1] == L'\\';
    wchar_t* pattern = malloc((length + 3) * sizeof(wchar_t));
    if (!pattern) return false;
    memcpy(pattern, path, length * sizeof(wchar_t));
    /* Allocation reserves the longest suffix plus its terminator. */
    const wchar_t* suffix = trailing_separator ? L"*" : L"\\*";
    memcpy(pattern + length, suffix, (trailing_separator ? 2 : 3) * sizeof(*pattern));
    WIN32_FIND_DATAW entry;
    HANDLE scan = FindFirstFileW(pattern, &entry);
    free(pattern);
    if (scan == INVALID_HANDLE_VALUE) {
        if (GetLastError() != ERROR_FILE_NOT_FOUND) return false;
        return RemoveDirectoryW(path) != 0;
    }
    bool ok = true;
    do {
        if (!wcscmp(entry.cFileName, L".") || !wcscmp(entry.cFileName, L"..")) continue;
        size_t name_length = wcslen(entry.cFileName);
        size_t child_length = length + 1 + name_length + 1;
        wchar_t* child = malloc(child_length * sizeof(wchar_t));
        if (!child) { ok = false; break; }
        /* child_length includes a separator even when the parent already ends in one. */
        memcpy(child, path, length * sizeof(*child));
        size_t name_offset = length;
        if (!trailing_separator) child[name_offset++] = L'\\';
        memcpy(child + name_offset, entry.cFileName, (name_length + 1) * sizeof(*child));
        if (!rt_win_remove_tree_wide(child, missing_ok)) ok = false;
        free(child);
    } while (FindNextFileW(scan, &entry));
    if (GetLastError() != ERROR_NO_MORE_FILES) ok = false;
    if (!FindClose(scan)) ok = false;
    if (!RemoveDirectoryW(path)) ok = false;
    return ok;
}

static bool rt_win_remove_tree_utf8(const char* path, bool missing_ok, bool files_ok) {
    if (!path || !*path) return false;
    wchar_t* wide = rt_win_long_path_widen(path);
    if (!wide) return false;
    /* Prefix even a short root: its descendants may grow beyond MAX_PATH.
       Normalize separators before using the extended path namespace. */
    for (wchar_t* p = wide; *p; ++p) if (*p == L'/') *p = L'\\';
    if (!(wide[0] == L'\\' && wide[1] == L'\\' && wide[2] == L'?' && wide[3] == L'\\')) {
        DWORD need = GetFullPathNameW(wide, 0, NULL, NULL);
        if (!need) { free(wide); return false; }
        wchar_t* full = malloc((size_t)need * sizeof(wchar_t));
        if (!full) { free(wide); return false; }
        DWORD got = GetFullPathNameW(wide, need, full, NULL);
        free(wide);
        if (!got || got >= need) { free(full); return false; }
        wide = malloc(((size_t)got + 9) * sizeof(wchar_t));
        if (!wide) { free(full); return false; }
        /* got excludes NUL; the allocation reserves even the longer UNC prefix. */
        if (full[0] == L'\\' && full[1] == L'\\') {
            memcpy(wide, L"\\\\?\\UNC\\", 8 * sizeof(*wide));
            memcpy(wide + 8, full + 2, ((size_t)got - 1) * sizeof(*wide));
        } else {
            memcpy(wide, L"\\\\?\\", 4 * sizeof(*wide));
            memcpy(wide + 4, full, ((size_t)got + 1) * sizeof(*wide));
        }
        free(full);
    }
    DWORD attrs = GetFileAttributesW(wide);
    bool ok = false;
    if (attrs == INVALID_FILE_ATTRIBUTES || files_ok ||
        (attrs & (FILE_ATTRIBUTE_DIRECTORY | FILE_ATTRIBUTE_REPARSE_POINT)))
        ok = rt_win_remove_tree_wide(wide, missing_ok);
    free(wide);
    return ok;
}
#endif
