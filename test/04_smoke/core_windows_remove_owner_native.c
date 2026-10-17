/* Deletes only CREATE_NEW fixtures inside the explicit owned evidence scratch. */
#include "runtime.h"
#include <windows.h>
#include <errno.h>
#include <stdio.h>
#include <wchar.h>
extern int64_t rt_remove(int64_t path);

static int64_t tagged_path(const wchar_t *path) {
    char utf8[2048];
    int length = WideCharToMultiByte(CP_UTF8, 0, path, -1, utf8, sizeof(utf8), NULL, NULL);
    return length > 0 ? rt_string_new((const uint8_t*)utf8, (uint64_t)length - 1) : 0;
}

int main(void) {
    const wchar_t *root = L"C:\\dev\\simple-bootstrap-storage\\phase3-validation-20261016\\core-remove-owner-regression\\scratch\\";
    wchar_t file[1024], directory[1024];
    _snwprintf(file, 1024, L"%lsowned-%lu space-\xD55C\xAE00.tmp", root, GetCurrentProcessId());
    _snwprintf(directory, 1024, L"%lsowned-%lu empty-\xD55C\xAE00", root, GetCurrentProcessId());
    /* Fixed absolute parent and fixed child names; never consume a user path. */
    if (wcsncmp(file, root, wcslen(root)) != 0 || wcsncmp(directory, root, wcslen(root)) != 0) return 10;
    HANDLE created = CreateFileW(file, GENERIC_WRITE, 0, NULL, CREATE_NEW, FILE_ATTRIBUTE_NORMAL, NULL);
    if (created == INVALID_HANDLE_VALUE) return 11;
    DWORD written = 0;
    BOOL wrote = WriteFile(created, "owned", 5, &written, NULL);
    CloseHandle(created);
    if (!wrote || written != 5) return 12;
    if (GetFileAttributesW(file) == INVALID_FILE_ATTRIBUTES) return 13;
    int64_t path = tagged_path(file);
    if (rt_remove(path) != 0) return 14;
    if (GetFileAttributesW(file) != INVALID_FILE_ATTRIBUTES) return 15;
    if (GetLastError() != ERROR_FILE_NOT_FOUND) return 16;
    if (rt_remove(path) != -(int64_t)ENOENT) return 17;
    if (!CreateDirectoryW(directory, NULL)) return 18;
    if (rt_remove(tagged_path(directory)) != 0) return 19;
    if (GetFileAttributesW(directory) != INVALID_FILE_ATTRIBUTES) return 20;
    if (GetLastError() != ERROR_FILE_NOT_FOUND) return 21;
    puts("CORE_WINDOWS_REMOVE_OWNER_PASS file=deleted missing=ENOENT utf8_spaces=preserved empty_dir=deleted");
    return 0;
}
