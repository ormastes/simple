#include "../runtime.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#ifndef SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE
#define SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE 0x2
#endif
static int make_dir(const char *path) { return CreateDirectoryA(path, NULL) ? 0 : -1; }
static int remove_dir(const char *path) { return RemoveDirectoryA(path) ? 0 : -1; }
static int remove_file(const char *path) { return DeleteFileA(path) ? 0 : -1; }
static int move_file(const char *from, const char *to) { return MoveFileA(from, to) ? 0 : -1; }
static int create_temp_root(char *out, size_t cap) {
    char dir[MAX_PATH], file[MAX_PATH];
    DWORD n = GetTempPathA(MAX_PATH, dir);
    if (n == 0 || n >= MAX_PATH) return -1;
    if (GetTempFileNameA(dir, "fv", 0, file) == 0) return -1;
    if (!DeleteFileA(file) || !CreateDirectoryA(file, NULL)) return -1;
    size_t flen = strlen(file);
    if (flen >= cap) { RemoveDirectoryA(file); return -1; }
    memcpy(out, file, flen + 1);
    for (char *p = out; *p; ++p) {
        if (*p == '\\') *p = '/';
    }
    return 0;
}
static int write_exact_file(const char *path, const void *data, size_t len) {
    HANDLE h = CreateFileA(path, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    if (h == INVALID_HANDLE_VALUE) return -1;
    const uint8_t *p = (const uint8_t *)data;
    size_t done = 0;
    while (done < len) {
        DWORD chunk = (len - done) > 0x100000u ? 0x100000u : (DWORD)(len - done);
        DWORD written = 0;
        if (!WriteFile(h, p + done, chunk, &written, NULL) || written == 0) {
            CloseHandle(h);
            return -1;
        }
        done += written;
    }
    return CloseHandle(h) ? 0 : -1;
}
static int create_symlink_entry(const char *target, const char *linkpath, int is_dir) {
    DWORD flags = (is_dir ? SYMBOLIC_LINK_FLAG_DIRECTORY : 0) |
        SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE;
    if (CreateSymbolicLinkA(linkpath, target, flags)) return 0;
    return CreateSymbolicLinkA(linkpath, target, is_dir ? SYMBOLIC_LINK_FLAG_DIRECTORY : 0) ? 0 : -1;
}
#else
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
static int make_dir(const char *path) { return mkdir(path, 0700); }
static int remove_dir(const char *path) { return rmdir(path); }
static int remove_file(const char *path) { return unlink(path); }
static int move_file(const char *from, const char *to) { return rename(from, to); }
static int create_temp_root(char *out, size_t cap) {
    char tmpl[] = "/tmp/simple-file-view-XXXXXX";
    if (cap <= sizeof(tmpl)) return -1;
    memcpy(out, tmpl, sizeof(tmpl));
    return mkdtemp(out) ? 0 : -1;
}
static int write_exact_file(const char *path, const void *data, size_t len) {
    int fd = open(path, O_CREAT | O_TRUNC | O_WRONLY, 0600);
    if (fd < 0) return -1;
    const uint8_t *p = (const uint8_t *)data;
    size_t done = 0;
    while (done < len) {
        ssize_t n = write(fd, p + done, len - done);
        if (n <= 0) { close(fd); return -1; }
        done += (size_t)n;
    }
    return close(fd) == 0 ? 0 : -1;
}
static int create_symlink_entry(const char *target, const char *linkpath, int is_dir) {
    (void)is_dir;
    return symlink(target, linkpath);
}
#endif

typedef struct { const uint8_t *data; int64_t len; } TestText;

const uint8_t *rt_string_data(int64_t value) { return ((TestText *)(uintptr_t)value)->data; }
int64_t rt_string_len(int64_t value) { return ((TestText *)(uintptr_t)value)->len; }

SplArray *rt_array_new(int64_t cap) {
    SplArray *a = calloc(1, sizeof(*a));
    if (!a) return NULL;
    a->cap = cap;
    a->items = cap ? calloc((size_t)cap, sizeof(*a->items)) : NULL;
    if (cap && !a->items) { free(a); return NULL; }
    return a;
}

static int packed_array_creations;

SplArray *rt_byte_array_new_len(uint64_t len) {
    if (len > INT64_MAX) return NULL;
    SplArray *array = rt_array_new((int64_t)len);
    if (array) {
        array->len = (int64_t)len;
        packed_array_creations++;
    }
    return array;
}

void rt_array_free(SplArray *a) { if (a) { free(a->items); free(a); } }

int8_t rt_array_push(SplArray *a, int64_t value) {
    if (!a || a->len >= a->cap) return 0;
    a->items[a->len++].as_int = value;
    return 1;
}

int8_t rt_array_set(SplArray *a, int64_t idx, int64_t value) {
    if (!a || idx < 0 || idx >= a->len) return 0;
    a->items[idx].as_int = value;
    return 1;
}

static TestText text(const char *value) {
    TestText result = {(const uint8_t *)value, (int64_t)strlen(value)};
    return result;
}

static int64_t tval(const TestText *t) { return (int64_t)(uintptr_t)t; }

static void assert_bytes_eq(int64_t raw, const uint8_t *expected, size_t len) {
    assert(raw != 3);
    SplArray *bytes = (SplArray *)(uintptr_t)raw;
    assert(bytes && (size_t)bytes->len == len);
    for (size_t i = 0; i < len; ++i) {
        assert((uint8_t)(bytes->items[i].as_int >> 3) == expected[i]);
    }
    rt_array_free(bytes);
}

int main(void) {
    char root[512];
    assert(create_temp_root(root, sizeof(root)) == 0);
    char nested[600], file[700], empty_file[700], big_file[700], old_file[700];
    char link_path[700], dir_link[700], root_slash[600];
    snprintf(nested, sizeof(nested), "%s/nested", root);
    snprintf(file, sizeof(file), "%s/data.bin", nested);
    snprintf(empty_file, sizeof(empty_file), "%s/empty.bin", nested);
    snprintf(big_file, sizeof(big_file), "%s/big.bin", nested);
    snprintf(old_file, sizeof(old_file), "%s/old.bin", nested);
    snprintf(link_path, sizeof(link_path), "%s/link.bin", nested);
    snprintf(dir_link, sizeof(dir_link), "%s/dir_link", root);
    snprintf(root_slash, sizeof(root_slash), "%s/", root);

    assert(make_dir(nested) == 0);
    assert(write_exact_file(file, "abcdef", 6) == 0);
    assert(write_exact_file(empty_file, "", 0) == 0);

    const size_t big_len = 70000;
    uint8_t *big_data = (uint8_t *)malloc(big_len);
    assert(big_data != NULL);
    for (size_t i = 0; i < big_len; ++i) big_data[i] = (uint8_t)((i * 31 + 7) & 0xFFu);
    assert(write_exact_file(big_file, big_data, big_len) == 0);

    int symlink_made = (create_symlink_entry("data.bin", link_path, 0) == 0);
    int dir_symlink_made = (create_symlink_entry("nested", dir_link, 1) == 0);
    if (!symlink_made || !dir_symlink_made) {
        fprintf(stderr, "note: symlink creation unavailable; skipping symlink assertions\n");
    }

    TestText root_text = text(root), path_text = text("nested/data.bin");
    int64_t handle = rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&path_text));
    assert(handle > 0);
    assert(rt_file_view_mapping_supported_v1(handle) == 1);
    assert(rt_file_view_size_v1(handle) == 6);
    int64_t orig_dev = rt_file_view_device_v1(handle);
    int64_t orig_ino = rt_file_view_inode_v1(handle);
    assert(orig_dev >= 0);
    assert(orig_ino >= 0);
    assert(rt_file_view_prefetch_v1(handle, 1, 3) == 1);
    assert(rt_file_view_prefetch_v1(handle, 5, 2) == 0);

    assert_bytes_eq(rt_file_view_pread_exact_v1(handle, 1, 3), (const uint8_t *)"bcd", 3);
    assert(packed_array_creations == 1);
    assert_bytes_eq(rt_file_view_map_copy_v1(handle, 2, 3), (const uint8_t *)"cde", 3);
    assert(packed_array_creations == 2);
    assert_bytes_eq(rt_file_view_pread_exact_v1(handle, 6, 0), (const uint8_t *)"", 0);
    assert_bytes_eq(rt_file_view_map_copy_v1(handle, 6, 0), (const uint8_t *)"", 0);

    assert(rt_file_view_pread_exact_v1(handle, 5, 2) == 3);
    assert(rt_file_view_map_copy_v1(handle, 5, 2) == 3);
    assert(rt_file_view_pread_exact_v1(handle, UINT64_MAX, 1) == 3);
    assert(rt_file_view_map_copy_v1(handle, 0, UINT64_MAX) == 3);

    /* Path replacement must leave open handle pinned to original inode and bytes. */
    assert(move_file(file, old_file) == 0);
    assert(write_exact_file(file, "REPLACEMENT", 11) == 0);
    assert(rt_file_view_device_v1(handle) == orig_dev);
    assert(rt_file_view_inode_v1(handle) == orig_ino);
    assert(rt_file_view_size_v1(handle) == 6);
    assert_bytes_eq(rt_file_view_pread_exact_v1(handle, 0, 6), (const uint8_t *)"abcdef", 6);
    assert_bytes_eq(rt_file_view_map_copy_v1(handle, 0, 6), (const uint8_t *)"abcdef", 6);
    assert(remove_file(file) == 0);
    assert(move_file(old_file, file) == 0);

    assert(rt_file_view_close_v1(handle) == 1);
    assert(rt_file_view_close_v1(handle) == 0);
    assert(rt_file_view_size_v1(handle) == -1);
    assert(rt_file_view_mapping_supported_v1(handle) == 0);
    assert(rt_file_view_pread_exact_v1(handle, 0, 0) == 3);
    assert(rt_file_view_size_v1(-1) == -1);
    assert(rt_file_view_close_v1(-1) == 0);

    /* Empty file mapping and pread check. */
    TestText empty_text = text("nested/empty.bin");
    int64_t empty_h = rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&empty_text));
    assert(empty_h > 0);
    assert(rt_file_view_size_v1(empty_h) == 0);
    assert_bytes_eq(rt_file_view_pread_exact_v1(empty_h, 0, 0), (const uint8_t *)"", 0);
    assert_bytes_eq(rt_file_view_map_copy_v1(empty_h, 0, 0), (const uint8_t *)"", 0);
    assert(rt_file_view_pread_exact_v1(empty_h, 0, 1) == 3);
    assert(rt_file_view_close_v1(empty_h) == 1);

    /* Granularity-aligned offset map_copy and pread on >64KB file. */
    TestText big_text = text("nested/big.bin");
    int64_t big_h = rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&big_text));
    assert(big_h > 0);
    assert(rt_file_view_size_v1(big_h) == (int64_t)big_len);
    assert_bytes_eq(rt_file_view_map_copy_v1(big_h, 65540, 256), big_data + 65540, 256);
    assert_bytes_eq(rt_file_view_pread_exact_v1(big_h, 65540, 256), big_data + 65540, 256);
    assert(rt_file_view_close_v1(big_h) == 1);
    free(big_data);

    /* Pinned archive alias + absolute prefix beneath root. */
    TestText abs_file = text(file);
    int64_t pinned_h = rt_pinned_archive_open_beneath_v1(tval(&root_text), tval(&abs_file));
    assert(pinned_h > 0);
    assert(rt_pinned_archive_size_v1(pinned_h) == 6);
    assert(rt_pinned_archive_device_v1(pinned_h) >= 0);
    assert(rt_pinned_archive_inode_v1(pinned_h) >= 0);
    assert(rt_pinned_archive_close_v1(pinned_h) == 1);

    /* Trailing slash on root, directory as leaf, missing file. */
    TestText root_slash_text = text(root_slash);
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_slash_text), tval(&path_text)) == -2);
    TestText dir_leaf = text("nested");
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&dir_leaf)) == -3);
    TestText missing = text("nested/missing.bin");
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&missing)) == -1);

    if (symlink_made) {
        TestText link_text = text("nested/link.bin");
        assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&link_text)) == -3);
    }
    if (dir_symlink_made) {
        TestText dir_link_file = text("dir_link/data.bin");
        assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&dir_link_file)) == -3);
        char dir_link_slash[720];
        snprintf(dir_link_slash, sizeof(dir_link_slash), "%s/", dir_link);
        TestText dir_link_slash_t = text(dir_link_slash), data_only = text("data.bin");
        assert(rt_file_view_open_beneath_no_follow_v1(tval(&dir_link_slash_t), tval(&data_only)) < 0);
        TestText dir_link_t = text(dir_link);
        assert(rt_file_view_open_beneath_no_follow_v1(tval(&dir_link_t), tval(&data_only)) == -3);
    }

    TestText escape_text = text("../data.bin");
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&escape_text)) == -2);
    TestText mid_dotdot = text("nested/../nested/data.bin");
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&mid_dotdot)) == -2);
    TestText mid_dot = text("nested/./data.bin");
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&mid_dot)) == -2);
    const uint8_t invalid_root_bytes[] = {'b', 'a', 'd', 0, 'r', 'o', 'o', 't'};
    TestText invalid_root = {invalid_root_bytes, 8};
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&invalid_root), tval(&path_text)) == -2);
    const uint8_t invalid_path_bytes[] = {'b', 'a', 'd', 0, 'p', 'a', 't', 'h'};
    TestText invalid_path = {invalid_path_bytes, 8};
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&invalid_path)) == -2);

#if defined(_WIN32)
    /* Windows-specific: mixed separators, case-insensitive drive prefix,
     * drive-relative, UNC escape, rooted without drive, and NTFS ADS. */
    size_t file_len = strlen(file);
    if (file_len > 3 && file_len < 700 && file[1] == ':') {
        char flipped[700];
        memcpy(flipped, file, file_len + 1);
        flipped[0] = (flipped[0] >= 'A' && flipped[0] <= 'Z')
            ? (char)(flipped[0] + ('a' - 'A')) : (char)(flipped[0] - ('a' - 'A'));
        for (char *p = flipped; *p; ++p) if (*p == '/') *p = '\\';
        TestText flipped_text = text(flipped);
        int64_t win_h = rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&flipped_text));
        assert(win_h > 0);
        assert_bytes_eq(rt_file_view_pread_exact_v1(win_h, 0, 6), (const uint8_t *)"abcdef", 6);
        assert(rt_file_view_close_v1(win_h) == 1);
    }
    TestText backslash_rel = text("nested\\data.bin");
    int64_t bs_h = rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&backslash_rel));
    assert(bs_h > 0);
    assert(rt_file_view_close_v1(bs_h) == 1);

    TestText drive_rel = text("C:nested/data.bin");
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&drive_rel)) == -2);
    TestText unc1 = text("//localhost/c$/Windows/win.ini");
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&unc1)) == -2);
    TestText unc2 = text("\\\\localhost\\c$\\Windows\\win.ini");
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&unc2)) == -2);
    TestText rooted_no_drive = text("/etc/passwd");
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&rooted_no_drive)) == -2);
    TestText ads_path = text("nested/data.bin:stream");
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&ads_path)) == -2);
    TestText bad_colon_root = text("1:stream");
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&bad_colon_root), tval(&path_text)) == -2);
    const uint8_t invalid_utf8_bytes[] = {0xFFu, 0xFEu, 'b', 'a', 'd'};
    TestText invalid_utf8 = {invalid_utf8_bytes, 5};
    assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&invalid_utf8)) == -2);
#endif

    /* Exhaust all 1024 table slots, verify slot-1025 fails cleanly, then reuse
     * one freed slot and verify stale generation-tagged handles stay invalid. */
    {
        int64_t pool_handles[1024];
        int pool_count = 0;
        for (int i = 0; i < 1024; ++i) {
            int64_t ph = rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&path_text));
            if (ph < 0) break;
            pool_handles[pool_count++] = ph;
        }
#if defined(_WIN32)
        assert(pool_count == 1024);
        assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&path_text)) == -1);
#else
        /* Low RLIMIT_NOFILE shells (e.g. macOS 256 or Linux 1024) hit EMFILE
         * before exhausting all 1024 slots; still verify overflow when reached. */
        assert(pool_count >= 16);
        if (pool_count == 1024) {
            assert(rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&path_text)) == -1);
        }
#endif
        int64_t recycled_old = pool_handles[0];
        assert(rt_file_view_close_v1(recycled_old) == 1);
        int64_t recycled_new = rt_file_view_open_beneath_no_follow_v1(tval(&root_text), tval(&path_text));
        assert(recycled_new > 0);
        assert(recycled_new != recycled_old);
        assert(rt_file_view_close_v1(recycled_old) == 0);
        assert(rt_file_view_size_v1(recycled_old) == -1);
        pool_handles[0] = recycled_new;
        for (int i = 0; i < pool_count; ++i) {
            assert(rt_file_view_close_v1(pool_handles[i]) == 1);
        }
    }

    if (dir_symlink_made) assert(remove_dir(dir_link) == 0);
    if (symlink_made) assert(remove_file(link_path) == 0);
    assert(remove_file(big_file) == 0);
    assert(remove_file(empty_file) == 0);
    assert(remove_file(file) == 0);
    assert(remove_dir(nested) == 0);
    assert(remove_dir(root) == 0);
    puts("rt_file_view_selfcheck: PASS");
    return 0;
}
