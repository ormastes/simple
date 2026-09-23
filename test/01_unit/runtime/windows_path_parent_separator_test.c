#include "runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if !defined(_WIN32)
#error "windows_path_parent_separator_test.c requires a Windows target"
#endif

static int failures = 0;

extern int rt_path_parent_is_separator_for_test(uint8_t byte, int windows);

static void expect_parent(const char* path, const char* expected) {
    int64_t value = rt_path_parent((const uint8_t*)path, (int64_t)strlen(path));
    int64_t actual_len = rt_string_len(value);
    const uint8_t* actual = rt_string_data(value);
    size_t expected_len = strlen(expected);
    if (actual_len != (int64_t)expected_len ||
            (expected_len != 0 && (!actual || memcmp(actual, expected, expected_len) != 0))) {
        fprintf(stderr, "FAIL path=%s expected=%s actual=%.*s actual_len=%lld\n",
                path, expected, (int)(actual_len > 0 ? actual_len : 0),
                actual ? (const char*)actual : "", (long long)actual_len);
        failures++;
    }
}

int main(void) {
    if (!rt_path_parent_is_separator_for_test((uint8_t)'\\', 1) ||
            rt_path_parent_is_separator_for_test((uint8_t)'\\', 0) ||
            !rt_path_parent_is_separator_for_test((uint8_t)'/', 0)) {
        fputs("FAIL platform separator policy\n", stderr);
        failures++;
    }
    expect_parent("C:\\workspace\\src\\main.spl", "C:\\workspace\\src");
    expect_parent("C:/workspace\\src/main.spl", "C:/workspace\\src");
    expect_parent("C:\\workspace\\src\\", "C:\\workspace");
    expect_parent("C:\\작업\\소스\\main.spl", "C:\\작업\\소스");
    expect_parent("\\\\server\\share\\src\\main.spl", "\\\\server\\share\\src");
    expect_parent("C:\\file.spl", "C:\\");
    expect_parent("C:\\", "");
    expect_parent("\\\\server\\share", "");
    expect_parent("\\\\server\\share\\", "");
    expect_parent("\\\\server\\share\\file.spl", "\\\\server\\share\\");
    expect_parent("\\\\?\\C:\\file.spl", "\\\\?\\C:\\");
    expect_parent("\\\\?\\UNC\\server\\share\\file.spl", "\\\\?\\UNC\\server\\share\\");
    expect_parent("relative.spl", ".");

    if (failures != 0) return 1;
    puts("windows-path-parent-separator: PASS");
    return 0;
}
