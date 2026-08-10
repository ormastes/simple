/* Behavior gate for the four-word text ABI used by rt_file_rename/move.
 *
 * Each path is passed as (pointer,length), with the length excluding the
 * trailing C sentinel.  The test deliberately passes exact-length buffers so
 * a two-pointer implementation cannot accidentally appear to work.
 */
#include "../runtime.h"

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

int main(void) {
    const char* dir = "simple-rt-file-rename-move-selfcheck.tmp";
    const char* source = "simple-rt-file-rename-move-selfcheck.tmp/source.txt";
    const char* renamed = "simple-rt-file-rename-move-selfcheck.tmp/renamed.txt";
    const char* moved = "simple-rt-file-rename-move-selfcheck.tmp/moved.txt";
    const char source_exact[] = "simple-rt-file-rename-move-selfcheck.tmp/source.txt";
    const char renamed_exact[] = "simple-rt-file-rename-move-selfcheck.tmp/renamed.txt";
    const char moved_exact[] = "simple-rt-file-rename-move-selfcheck.tmp/moved.txt";

    remove(source);
    remove(renamed);
    remove(moved);
    RMDIR(dir);
    if (MKDIR(dir) != 0 && errno != EEXIST) {
        printf("SELFCHECK FAILED (cannot create %s)\n", dir);
        return 1;
    }

    check(write_file(source, "rename-move ABI payload"), "source fixture created");
    check(rt_file_rename((const uint8_t*)source_exact, path_length(source_exact),
                         (const uint8_t*)renamed_exact, path_length(renamed_exact)) == 1,
          "rename accepts four text words");
    check(!file_exists(source) && file_is(renamed, "rename-move ABI payload"),
          "rename moves the exact source and preserves content");

    check(rt_file_move((const uint8_t*)renamed_exact, path_length(renamed_exact),
                       (const uint8_t*)moved_exact, path_length(moved_exact)) == 1,
          "move accepts four text words");
    check(!file_exists(renamed) && file_is(moved, "rename-move ABI payload"),
          "move aliases the same exact-path behavior");

    const uint8_t embedded_nul[] = {'s', 'o', '\0', 'u', 'r', 'c', 'e'};
    check(rt_file_rename(embedded_nul, sizeof(embedded_nul),
                         (const uint8_t*)renamed_exact, path_length(renamed_exact)) == 0,
          "embedded NUL path is rejected");
    check(rt_file_rename(NULL, 1, (const uint8_t*)renamed_exact, path_length(renamed_exact)) == 0,
          "null pointer with nonzero length is rejected");

    remove(source);
    remove(renamed);
    remove(moved);
    RMDIR(dir);
    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
