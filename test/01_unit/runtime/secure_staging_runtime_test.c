#include "runtime.h"
#if !defined(_WIN32)
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

int main(void) {
    char parent[] = "/tmp/simple-secure-stage-test-XXXXXX";
    assert(mkdtemp(parent) != NULL);
    int64_t value = rt_secure_temp_dir((const uint8_t*)parent, strlen(parent), (const uint8_t*)"llvm", 4);
    const char* staging = (const char*)rt_string_data(value);
    struct stat metadata;
    assert(staging && stat(staging, &metadata) == 0 && S_ISDIR(metadata.st_mode));
    assert((metadata.st_mode & 0777) == 0700);
    char source[320], destination[320];
    snprintf(source, sizeof(source), "%s/module.o", staging);
    snprintf(destination, sizeof(destination), "%s/module.o", parent);
    FILE* file = fopen(source, "wb");
    assert(file && fwrite("staged", 1, 6, file) == 6 && fclose(file) == 0);
    assert(rt_file_publish_noreplace((const uint8_t*)source, strlen(source), (const uint8_t*)destination, strlen(destination)) == 1);
    assert(access(source, F_OK) != 0 && access(destination, F_OK) == 0);
    file = fopen(source, "wb");
    assert(file && fclose(file) == 0);
    assert(rt_file_publish_noreplace((const uint8_t*)source, strlen(source), (const uint8_t*)destination, strlen(destination)) == 0);
    assert(access(source, F_OK) == 0);
    assert(rt_file_publish_noreplace((const uint8_t*)"/missing/staged", 15, (const uint8_t*)"/missing/destination", 20) == -1);
    assert(unlink(source) == 0 && unlink(destination) == 0 && rmdir(staging) == 0 && rmdir(parent) == 0);
    return 0;
}
#else
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <windows.h>

/* This focused executable links runtime_secure_staging.c without the full
 * runtime archive. rt_secure_temp_dir owns this unrelated constructor call. */
int64_t rt_string_new(const uint8_t* data, uint64_t len) {
    (void)data;
    (void)len;
    return 0;
}

static void widen_extended(const char* path, wchar_t* out, size_t capacity) {
    wchar_t wide[32768];
    int count = MultiByteToWideChar(CP_UTF8, 0, path, -1, wide, 32768);
    assert(count > 0 && capacity > (size_t)count + 4);
    out[0] = L'\\'; out[1] = L'\\'; out[2] = L'?'; out[3] = L'\\';
    memcpy(out + 4, wide, (size_t)count * sizeof(wchar_t));
}

static void create_long_file(const char* path, const char* bytes) {
    wchar_t wide[32768];
    widen_extended(path, wide, 32768);
    HANDLE file = CreateFileW(wide, GENERIC_WRITE, 0, NULL, CREATE_NEW,
                              FILE_ATTRIBUTE_NORMAL, NULL);
    assert(file != INVALID_HANDLE_VALUE);
    DWORD written = 0;
    DWORD length = (DWORD)strlen(bytes);
    assert(WriteFile(file, bytes, length, &written, NULL) && written == length);
    assert(CloseHandle(file));
}

int main(void) {
    char temp[MAX_PATH], base[512], dirs[3][1024], source[1200], destination[1200];
    wchar_t wide[32768];
    assert(GetTempPathA(MAX_PATH, temp) > 0);
    snprintf(base, sizeof(base), "%ssimple-publish-long-%lu", temp, (unsigned long)GetCurrentProcessId());
    assert(CreateDirectoryA(base, NULL) || GetLastError() == ERROR_ALREADY_EXISTS);
    strcpy(dirs[0], base);
    for (int i = 0; i < 3; i++) {
        snprintf(dirs[i], sizeof(dirs[i]), "%s\\segment-%d-abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdefghij",
                 i == 0 ? base : dirs[i - 1], i);
        widen_extended(dirs[i], wide, 32768);
        assert(CreateDirectoryW(wide, NULL));
    }
    snprintf(source, sizeof(source), "%s\\staged.module.o", dirs[2]);
    snprintf(destination, sizeof(destination), "%s\\published.module.o", dirs[2]);
    assert(strlen(source) > 260 && strlen(destination) > 260);

    create_long_file(source, "staged");
    assert(rt_file_publish_noreplace((const uint8_t*)source, strlen(source),
                                     (const uint8_t*)destination, strlen(destination)) == 1);
    widen_extended(source, wide, 32768);
    assert(GetFileAttributesW(wide) == INVALID_FILE_ATTRIBUTES);
    widen_extended(destination, wide, 32768);
    assert(GetFileAttributesW(wide) != INVALID_FILE_ATTRIBUTES);

    create_long_file(source, "second");
    assert(rt_file_publish_noreplace((const uint8_t*)source, strlen(source),
                                     (const uint8_t*)destination, strlen(destination)) == 0);
    widen_extended(source, wide, 32768); assert(DeleteFileW(wide));
    widen_extended(destination, wide, 32768); assert(DeleteFileW(wide));
    for (int i = 2; i >= 0; i--) {
        widen_extended(dirs[i], wide, 32768); assert(RemoveDirectoryW(wide));
    }
    assert(RemoveDirectoryA(base));
    return 0;
}
#endif
