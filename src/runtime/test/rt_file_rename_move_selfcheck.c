/* Behavior gate for the four-word text ABI used by rt_file_rename/move.
 *
 * Each path is passed as (pointer,length), with the length excluding the
 * trailing C sentinel.  The test deliberately passes exact-length buffers so
 * a two-pointer implementation cannot accidentally appear to work.
 */
#if defined(SIMPLE_RT_FILE_MOVE_RENAME_ONLY)
#include <stdint.h>
extern int8_t rt_file_rename(const uint8_t* src_ptr, uint64_t src_len,
                             const uint8_t* dst_ptr, uint64_t dst_len);
extern int8_t rt_file_move(const uint8_t* src_ptr, uint64_t src_len,
                           const uint8_t* dst_ptr, uint64_t dst_len);
#else
#include "../runtime.h"
#endif

#include <errno.h>
#include <stdio.h>
#include <string.h>

#if defined(_WIN32)
#include <direct.h>
#define MKDIR(path) _mkdir(path)
#define RMDIR(path) _rmdir(path)
#else
#include <sys/stat.h>
#include <unistd.h>
#define MKDIR(path) mkdir(path, 0700)
#define RMDIR(path) rmdir(path)
#endif

static int failures;

static void check(int condition, const char* label) {
    if (condition) {
        printf("  ok   %s\n", label);
    } else {
        printf("  FAIL %s\n", label);
        failures++;
    }
}

static int write_file(const char* path, const char* contents) {
    FILE* file = fopen(path, "wb");
    if (!file) return 0;
    size_t length = strlen(contents);
    int ok = fwrite(contents, 1, length, file) == length;
    ok = fclose(file) == 0 && ok;
    return ok;
}

static int file_exists(const char* path) {
    FILE* file = fopen(path, "rb");
    if (!file) return 0;
    fclose(file);
    return 1;
}

static int file_is(const char* path, const char* expected) {
    FILE* file = fopen(path, "rb");
    if (!file) return 0;
    char buffer[64];
    size_t length = fread(buffer, 1, sizeof(buffer), file);
    int ok = fclose(file) == 0;
    size_t expected_length = strlen(expected);
    return ok && length == expected_length && memcmp(buffer, expected, length) == 0;
}

static size_t path_length(const char* path) {
    return strlen(path);
}

#if !defined(_WIN32)
static void check_cross_device_fallback(const char* source,
                                        const uint8_t* source_exact,
                                        size_t source_len) {
    static const char* candidates[] = {"/dev/shm", "/tmp", NULL};
    struct stat source_device;
    if (stat(".", &source_device) != 0) {
        printf("  skip cross-device fallback: source device unavailable\n");
        return;
    }

    const char* target_dir = NULL;
    for (size_t index = 0; candidates[index] != NULL; index++) {
        struct stat candidate_device;
        if (stat(candidates[index], &candidate_device) == 0 &&
            candidate_device.st_dev != source_device.st_dev &&
            access(candidates[index], W_OK) == 0) {
            target_dir = candidates[index];
            break;
        }
    }
    if (!target_dir) {
        printf("  skip cross-device fallback: distinct writable mount unavailable\n");
        return;
    }

    char destination[512];
    int length = snprintf(destination, sizeof(destination),
                          "%s/simple-rt-file-move-cross-device-%ld.tmp",
                          target_dir, (long)getpid());
    check(length > 0 && (size_t)length < sizeof(destination),
          "cross-device destination path fits");
    if (length <= 0 || (size_t)length >= sizeof(destination)) return;
    remove(destination);

    check(write_file(source, "cross-device payload"),
          "cross-device source fixture created");
#if defined(SIMPLE_RT_FILE_MOVE_RENAME_ONLY)
    check(rt_file_move(source_exact, source_len,
                       (const uint8_t*)destination, (size_t)length) == 0,
          "rename-only move reports the EXDEV boundary");
    check(file_is(source, "cross-device payload") && !file_exists(destination),
          "rename-only EXDEV failure preserves source and destination");
#else
    check(rt_file_move(source_exact, source_len,
                       (const uint8_t*)destination, (size_t)length) == 1,
          "move takes the EXDEV copy-publication fallback");
    check(!file_exists(source) && file_is(destination, "cross-device payload"),
          "cross-device fallback publishes before source removal");
#endif
    remove(source);
    remove(destination);
}
#endif

int main(void) {
    const char* dir = "simple-rt-file-rename-move-selfcheck.tmp";
    const char* source = "simple-rt-file-rename-move-selfcheck.tmp/source.txt";
    const char* renamed = "simple-rt-file-rename-move-selfcheck.tmp/renamed.txt";
    const char* moved = "simple-rt-file-rename-move-selfcheck.tmp/moved.txt";
    const char* protected_dir = "simple-rt-file-rename-move-selfcheck.tmp/protected";
    const uint8_t source_exact[sizeof("simple-rt-file-rename-move-selfcheck.tmp/source.txt") - 1] =
        "simple-rt-file-rename-move-selfcheck.tmp/source.txt";
    const uint8_t renamed_exact[sizeof("simple-rt-file-rename-move-selfcheck.tmp/renamed.txt") - 1] =
        "simple-rt-file-rename-move-selfcheck.tmp/renamed.txt";
    const uint8_t moved_exact[sizeof("simple-rt-file-rename-move-selfcheck.tmp/moved.txt") - 1] =
        "simple-rt-file-rename-move-selfcheck.tmp/moved.txt";

    remove(source);
    remove(renamed);
    remove(moved);
    RMDIR(protected_dir);
    RMDIR(dir);
    if (MKDIR(dir) != 0 && errno != EEXIST) {
        printf("SELFCHECK FAILED (cannot create %s)\n", dir);
        return 1;
    }

    check(write_file(source, "rename-move ABI payload"), "source fixture created");
    check(rt_file_rename(source_exact, sizeof(source_exact),
                         renamed_exact, sizeof(renamed_exact)) == 1,
          "rename accepts four text words without C-string sentinels");
    check(!file_exists(source) && file_is(renamed, "rename-move ABI payload"),
          "rename moves the exact source and preserves content");

    check(rt_file_move(renamed_exact, sizeof(renamed_exact),
                       moved_exact, sizeof(moved_exact)) == 1,
          "move accepts four text words without C-string sentinels");
    check(!file_exists(renamed) && file_is(moved, "rename-move ABI payload"),
          "move aliases the same exact-path behavior");

    check(write_file(renamed, "destination sentinel"),
          "pre-existing destination fixture created");
    check(rt_file_rename(source_exact, sizeof(source_exact),
                         renamed_exact, sizeof(renamed_exact)) == 0,
          "rename reports a missing source");
    check(file_is(renamed, "destination sentinel"),
          "failed rename preserves a pre-existing destination");
    check(rt_file_move(source_exact, sizeof(source_exact),
                       renamed_exact, sizeof(renamed_exact)) == 0,
          "move reports a missing source");
    check(file_is(renamed, "destination sentinel"),
          "failed move preserves a pre-existing destination");

    check(MKDIR(protected_dir) == 0, "pre-existing destination directory created");
    check(rt_file_move(source_exact, sizeof(source_exact),
                       (const uint8_t*)protected_dir, path_length(protected_dir)) == 0,
          "failed move rejects a destination directory");
    check(RMDIR(protected_dir) == 0,
          "failed move preserves a pre-existing destination directory");

    const uint8_t embedded_nul[] = {'s', 'o', '\0', 'u', 'r', 'c', 'e'};
    check(rt_file_rename(embedded_nul, sizeof(embedded_nul),
                         renamed_exact, sizeof(renamed_exact)) == 0,
          "embedded NUL path is rejected");
    check(rt_file_move(embedded_nul, sizeof(embedded_nul),
                       renamed_exact, sizeof(renamed_exact)) == 0,
          "move rejects an embedded NUL path");
    check(rt_file_rename(NULL, 1, renamed_exact, sizeof(renamed_exact)) == 0,
          "null pointer with nonzero length is rejected");

#if !defined(_WIN32)
    check_cross_device_fallback(source, source_exact, sizeof(source_exact));
#endif

    remove(source);
    remove(renamed);
    remove(moved);
    RMDIR(dir);
    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
