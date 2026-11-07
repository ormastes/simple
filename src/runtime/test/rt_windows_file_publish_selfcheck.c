/* Windows-only fixture: the Windows runner appends this after production helpers. */
#ifdef _WIN32
#include <windows.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <wchar.h>

/* Also let the C-runtime push guard parse this file as a standalone unit. */
int64_t rt_file_publish_noreplace(const uint8_t *staged_ptr, uint64_t staged_len,
                                  const uint8_t *destination_ptr, uint64_t destination_len);

static int failures;
static int checks;
static int cases;
static void require(int condition, const char *message) {
    checks++;
    if (!condition) {
        fprintf(stderr, "FAIL: %s (win32=%lu)\n", message, GetLastError());
        failures++;
    }
}
static void wide_absolute(const char *path, wchar_t *out) {
    wchar_t wide[4096], full[4096];
    require(MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, path, -1, wide, 4096) > 0, "fixture UTF-8 conversion");
    require(GetFullPathNameW(wide, 4096, full, NULL) > 0, "fixture absolute path");
    if (wcsncmp(full, L"\\\\?\\", 4) == 0) wcscpy(out, full);
    else swprintf(out, 4096, L"\\\\?\\%ls", full);
}
static void write_payload(const char *path, const char *payload) {
    wchar_t wide[4096]; wide_absolute(path, wide);
    HANDLE file = CreateFileW(wide, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, 0, NULL);
    require(file != INVALID_HANDLE_VALUE, "fixture create");
    if (file == INVALID_HANDLE_VALUE) return;
    DWORD count = 0;
    require(WriteFile(file, payload, (DWORD)strlen(payload), &count, NULL) && count == strlen(payload), "fixture write");
    require(CloseHandle(file), "fixture close");
}
static int payload_matches(const char *path, const char *payload) {
    wchar_t wide[4096]; wide_absolute(path, wide);
    HANDLE file = CreateFileW(wide, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, NULL);
    if (file == INVALID_HANDLE_VALUE) return 0;
    char bytes[32]; DWORD count = 0;
    int ok = ReadFile(file, bytes, sizeof(bytes), &count, NULL) && count == strlen(payload) && memcmp(bytes, payload, count) == 0;
    CloseHandle(file);
    return ok;
}
static int64_t publish(const char *from, const char *to) {
    return rt_file_publish_noreplace((const uint8_t*)from, strlen(from), (const uint8_t*)to, strlen(to));
}
static int path_missing(const char *path) {
    wchar_t wide[4096]; wide_absolute(path, wide);
    if (GetFileAttributesW(wide) != INVALID_FILE_ATTRIBUTES) return 0;
    DWORD error = GetLastError();
    return error == ERROR_FILE_NOT_FOUND || error == ERROR_PATH_NOT_FOUND;
}
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    char dir[4096], current[4096], relative_dir[4096] = "", staged[4096], destination[4096];
    wchar_t wide[4096], previous[4096];
    GetCurrentDirectoryW(4096, previous);
    /* UTF-8 Chinese and Korean components force the real W API path. */
    snprintf(dir, sizeof(dir), "%s\\fixture-%lu-\xe9\x95\xbf\xe8\xb7\xaf-\xed\x95\x9c\xea\xb8\x80", argv[1], GetCurrentProcessId());
    wide_absolute(dir, wide);
    require(CreateDirectoryW(wide, NULL), "fixture root");
    for (int i = 0; i < 12; i++) {
        strcat(dir, "\\publication-long-component");
        wide_absolute(dir, wide);
        require(CreateDirectoryW(wide, NULL), "fixture deep directory");
        if (i == 3) strcpy(current, dir);
        if (i >= 4) strcat(relative_dir, "publication-long-component\\");
    }
    require(strlen(dir) > 300, "fixture must exceed MAX_PATH");
    snprintf(staged, sizeof(staged), "%s\\staged-\xe6\xb1\x89\xe5\xad\x97.bin", dir);
    snprintf(destination, sizeof(destination), "%s\\published-\xed\x95\x9c\xea\xb8\x80.bin", dir);
    cases++;
    write_payload(staged, "first");
    require(publish(staged, destination) == 1, "absolute long Unicode publication");
    require(payload_matches(destination, "first"), "absolute Unicode published bytes");
    require(path_missing(staged), "successful publication consumes staged ownership");
    cases++;
    write_payload(staged, "second");
    require(publish(staged, destination) == 0, "existing destination must not be replaced");
    require(payload_matches(destination, "first") && payload_matches(staged, "second"), "collision preserves both files");
    require(MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, current, -1, wide, 4096) > 0, "fixture current directory conversion");
    require(SetCurrentDirectoryW(wide), "fixture enter current directory below MAX_PATH");
    snprintf(staged, sizeof(staged), "%srelative.bin", relative_dir);
    snprintf(destination, sizeof(destination), "%srelative-published.bin", relative_dir);
    require(strlen(destination) < 248, "relative input must stay below widening threshold");
    cases++;
    write_payload(staged, "relative");
    require(publish(staged, destination) == 1, "short relative input resolving beyond MAX_PATH");
    require(payload_matches(destination, "relative"), "relative published bytes");
    require(path_missing(staged), "relative publication consumes staged ownership");
    require(SetCurrentDirectoryW(previous), "fixture restore original directory");
    cases++;
    snprintf(staged, sizeof(staged), "%s\\error-staged.bin", dir);
    snprintf(destination, sizeof(destination), "%s\\missing-parent\\error-published.bin", dir);
    write_payload(staged, "error-source");
    require(publish(staged, destination) == -1, "missing destination parent reports an error");
    require(payload_matches(staged, "error-source"), "error preserves staged ownership and bytes");
    require(path_missing(destination), "error creates no destination");
    cases++;
    snprintf(staged, sizeof(staged), "%s\\missing-source.bin", dir);
    snprintf(destination, sizeof(destination), "%s\\missing-source-published.bin", dir);
    require(publish(staged, destination) == -1, "missing staged source reports an error");
    require(path_missing(staged) && path_missing(destination), "missing source creates no artifacts");
    printf("Windows publication: cases=%d checks=%d failures=%d\n", cases, checks, failures);
    return failures ? 1 : 0;
}
#endif /* _WIN32 */
