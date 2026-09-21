/* Appended after verbatim production publication helpers by the Windows runner. */
static int failures;
static void require(int condition, const char *message) {
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
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    char dir[4096], current[4096], relative_dir[4096] = "", staged[4096], destination[4096];
    wchar_t wide[4096], previous[4096];
    GetCurrentDirectoryW(4096, previous);
    snprintf(dir, sizeof(dir), "%s\\fixture-%lu", argv[1], GetCurrentProcessId());
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
    snprintf(staged, sizeof(staged), "%s\\staged.bin", dir);
    snprintf(destination, sizeof(destination), "%s\\published.bin", dir);
    write_payload(staged, "first");
    require(publish(staged, destination) == 1, "absolute long-path publication");
    require(payload_matches(destination, "first"), "absolute published bytes");
    write_payload(staged, "second");
    require(publish(staged, destination) == 0, "existing destination must not be replaced");
    require(payload_matches(destination, "first") && payload_matches(staged, "second"), "collision preserves both files");
    require(MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, current, -1, wide, 4096) > 0, "fixture current directory conversion");
    require(SetCurrentDirectoryW(wide), "fixture enter current directory below MAX_PATH");
    snprintf(staged, sizeof(staged), "%srelative.bin", relative_dir);
    snprintf(destination, sizeof(destination), "%srelative-published.bin", relative_dir);
    require(strlen(destination) < 248, "relative input must stay below widening threshold");
    write_payload(staged, "relative");
    require(publish(staged, destination) == 1, "short relative input resolving beyond MAX_PATH");
    require(payload_matches(destination, "relative"), "relative published bytes");
    SetCurrentDirectoryW(previous);
    printf("Windows publication: %d failures\n", failures);
    return failures ? 1 : 0;
}
