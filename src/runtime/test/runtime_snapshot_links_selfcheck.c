/* Focused hosted snapshot-link boundary. Build with function-section GC so
 * the unrelated core-host services are not pulled into this small executable. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../runtime_core_host_services.c"

int64_t rt_string_len(int64_t value) {
    return value ? (int64_t)strlen((const char*)(intptr_t)value) : -1;
}

const uint8_t* rt_string_data(int64_t value) {
    return (const uint8_t*)(intptr_t)value;
}

/* Unrelated hosted services in the same translation unit reference these;
 * the snapshot selfcheck never calls either stub. */
int64_t rt_string_new(const uint8_t* bytes, uint64_t len) {
    (void)bytes; (void)len;
    return 0;
}

int64_t rt_time_now_unix_micros(void) { return 0; }

static int64_t text_value(const char* value) {
    return (int64_t)(intptr_t)value;
}

static int check(int condition, const char* message) {
    if (!condition) fprintf(stderr, "snapshot-links: %s\n", message);
    return condition;
}

int main(void) {
#if defined(_WIN32)
    char root[MAX_PATH], target[MAX_PATH], other[MAX_PATH], link[MAX_PATH], directory[MAX_PATH];
    char dir_link[MAX_PATH], nested_link[MAX_PATH], chain[MAX_PATH], escaped[MAX_PATH];
    DWORD n = GetTempPathA(MAX_PATH, root);
    if (n == 0 || n + 32 >= MAX_PATH ||
        GetTempFileNameA(root, "snp", 0, root) == 0 || !DeleteFileA(root) ||
        !CreateDirectoryA(root, NULL)) return 2;
    for (char* p = root; *p; ++p) if (*p == '\\') *p = '/';
    snprintf(target, sizeof(target), "%s/target.txt", root);
    snprintf(other, sizeof(other), "%s/other.txt", root);
    snprintf(link, sizeof(link), "%s/link.txt", root);
    snprintf(directory, sizeof(directory), "%s/targetdir", root);
    snprintf(dir_link, sizeof(dir_link), "%s/dirlink", root);
    snprintf(nested_link, sizeof(nested_link), "%s/dirlink/nested", root);
    snprintf(chain, sizeof(chain), "%s/chain", root);
    snprintf(escaped, sizeof(escaped), "%s/escape", root);
    HANDLE file = CreateFileA(target, GENERIC_WRITE, 0, NULL, CREATE_NEW,
        FILE_ATTRIBUTE_NORMAL, NULL);
    if (file == INVALID_HANDLE_VALUE || !CloseHandle(file) ||
        !CreateDirectoryA(directory, NULL)) return 3;
    file = CreateFileA(other, GENERIC_WRITE, 0, NULL, CREATE_NEW,
        FILE_ATTRIBUTE_NORMAL, NULL);
    if (file == INVALID_HANDLE_VALUE || !CloseHandle(file)) return 3;
    int ok = 1;
    ok &= check(rt_snapshot_readonly_nofollow_v1(text_value(target), 1) == 0,
        "regular-file readonly failed");
    DWORD attrs = GetFileAttributesA(target);
    ok &= check(attrs != INVALID_FILE_ATTRIBUTES &&
        (attrs & FILE_ATTRIBUTE_READONLY) != 0, "readonly readback missing");
    ok &= check(rt_snapshot_readonly_nofollow_v1(text_value(directory), 2) != 0,
        "Windows directory readonly falsely qualified");
    int created = rt_snapshot_symlink_create_nofollow_v1(text_value(root),
        text_value(link), text_value("target.txt"), 1);
    if (created != 0) {
        fprintf(stderr, "snapshot-links: Windows symlink privilege unavailable\n");
        ok = 0;
    } else {
        ok &= check(rt_snapshot_symlink_match_nofollow_v1(text_value(root),
            text_value(link), text_value("target.txt"), 1) == 0,
            "exact file link readback failed");
        ok &= check(rt_snapshot_symlink_match_nofollow_v1(text_value(root),
            text_value(link), text_value("other.txt"), 1) != 0,
            "wrong raw target accepted");
        ok &= check(rt_snapshot_symlink_create_nofollow_v1(text_value(root),
            text_value(chain), text_value("link.txt"), 1) != 0,
            "symlink target chain accepted");
        ok &= check(rt_snapshot_readonly_nofollow_v1(text_value(link), 1) != 0,
            "readonly followed a symlink leaf");
        ok &= check(rt_snapshot_symlink_create_nofollow_v1(text_value(root),
            text_value(link), text_value("target.txt"), 1) != 0,
            "existing link replaced");
    }
    ok &= check(rt_snapshot_symlink_create_nofollow_v1(text_value(root),
        text_value(escaped), text_value("../outside"), 1) != 0,
        "escaping relative target accepted");
    if (rt_snapshot_symlink_create_nofollow_v1(text_value(root),
            text_value(dir_link), text_value("targetdir"), 2) == 0) {
        ok &= check(rt_snapshot_symlink_match_nofollow_v1(text_value(root),
            text_value(dir_link), text_value("targetdir"), 2) == 0,
            "directory link readback failed");
        ok &= check(rt_snapshot_symlink_create_nofollow_v1(text_value(root),
            text_value(nested_link), text_value("../target.txt"), 1) != 0,
            "reparse ancestor accepted");
        RemoveDirectoryA(dir_link);
    } else {
        fprintf(stderr, "snapshot-links: Windows directory symlink unavailable\n");
        ok = 0;
    }
    DeleteFileA(link);
    SetFileAttributesA(target, FILE_ATTRIBUTE_NORMAL);
    DeleteFileA(target);
    DeleteFileA(other);
    RemoveDirectoryA(directory);
    RemoveDirectoryA(root);
    return ok ? 0 : 1;
#else
    char root[] = "/tmp/simple-snapshot-links-XXXXXX";
    if (!mkdtemp(root)) return 2;
    char target[4096], other[4096], link[4096], directory[4096], dir_link[4096];
    char nested_link[4096], escaped[4096];
    snprintf(target, sizeof(target), "%s/target.txt", root);
    snprintf(other, sizeof(other), "%s/other.txt", root);
    snprintf(link, sizeof(link), "%s/link.txt", root);
    snprintf(directory, sizeof(directory), "%s/targetdir", root);
    snprintf(dir_link, sizeof(dir_link), "%s/dirlink", root);
    snprintf(nested_link, sizeof(nested_link), "%s/dirlink/nested", root);
    snprintf(escaped, sizeof(escaped), "%s/escape", root);
    FILE* file = fopen(target, "wb");
    if (!file || fclose(file) || mkdir(directory, 0700)) return 3;
    file = fopen(other, "wb");
    if (!file || fclose(file)) return 3;
    int ok = 1;
    ok &= check(rt_snapshot_readonly_nofollow_v1(text_value(target), 1) == 0,
        "POSIX regular-file readonly failed");
    struct stat info;
    ok &= check(stat(target, &info) == 0 && (info.st_mode & 0222) == 0,
        "POSIX readonly readback missing");
    ok &= check(rt_snapshot_symlink_create_nofollow_v1(text_value(root),
        text_value(link), text_value("target.txt"), 1) == 0,
        "POSIX file symlink create failed");
    ok &= check(rt_snapshot_symlink_match_nofollow_v1(text_value(root),
        text_value(link), text_value("target.txt"), 1) == 0,
        "POSIX exact link match failed");
    ok &= check(rt_snapshot_symlink_match_nofollow_v1(text_value(root),
        text_value(link), text_value("other.txt"), 1) != 0,
        "POSIX wrong link text accepted");
    ok &= check(rt_snapshot_readonly_nofollow_v1(text_value(link), 1) != 0,
        "POSIX readonly followed symlink leaf");
    ok &= check(rt_snapshot_symlink_create_nofollow_v1(text_value(root),
        text_value(escaped), text_value("../outside"), 1) != 0,
        "POSIX escaping link accepted");
    ok &= check(rt_snapshot_symlink_create_nofollow_v1(text_value(root),
        text_value(dir_link), text_value("targetdir"), 2) == 0,
        "POSIX dir symlink create failed");
    ok &= check(rt_snapshot_symlink_create_nofollow_v1(text_value(root),
        text_value(nested_link), text_value("../target.txt"), 1) != 0,
        "POSIX symlink ancestor accepted");
    unlink(dir_link);
    unlink(link);
    chmod(target, 0600);
    unlink(target);
    unlink(other);
    rmdir(directory);
    rmdir(root);
    return ok ? 0 : 1;
#endif
}
