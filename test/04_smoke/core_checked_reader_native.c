/* Real core-C checked-reader contract. Run with repository root as argv[1]. */
#include "runtime.h"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <windows.h>
#include <wchar.h>
extern int64_t rt_file_read_text_at_checked(int64_t, int64_t, int64_t);
extern int64_t rt_value_nil(void);

static int checks;
static int64_t text(const char *s) {
    return rt_string_new((const uint8_t *)s, (uint64_t)strlen(s));
}
static int expect_nil(int64_t value) {
    checks++;
    return value == 3 && value == rt_value_nil();
}
static int expect_bytes(int64_t value, const uint8_t *bytes, size_t size) {
    checks++;
    return value != 3 && rt_string_len(value) == (int64_t)size &&
        (size == 0 || memcmp(rt_string_data(value), bytes, size) == 0);
}
static int write_bytes(const char *path, const uint8_t *bytes, size_t size) {
    FILE *f = fopen(path, "wb");
    if (!f) return 0;
    size_t n = fwrite(bytes, 1, size, f);
    return fclose(f) == 0 && n == size;
}
int main(int argc, char **argv) {
    char fixture[4096];
    wchar_t wide[4096];
    uint8_t reference[1024];
    const uint8_t binary[] = {'A', 0, 0x1a, '\r', '\n', 0xc3, 0xa9, 'Z'};
    const uint8_t ascii[] = "abcdef";
    if (argc != 2) return 1;
    snprintf(fixture, sizeof(fixture), "%s/test/fixtures/compiled_tool_protocol/protocol caf\xc3\xa9.spl", argv[1]);
    if (!MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, fixture, -1, wide, 4096)) return 2;
    FILE *f = _wfopen(wide, L"rb");
    if (!f) return 3;
    size_t size = fread(reference, 1, sizeof(reference), f);
    int extra = fgetc(f);
    fclose(f);
    if (size != 297 || extra != EOF) return 4;
    if (!expect_bytes(rt_file_read_text_at_checked(text(fixture), 0, 1073741824), reference, size)) return 5;
    if (!expect_bytes(rt_file_read_text_at_checked(text(fixture), 7, 13), reference + 7, 13)) return 6;
    if (!write_bytes("checked-reader-ascii.tmp", ascii, 6) ||
        !write_bytes("checked-reader-binary.tmp", binary, sizeof(binary)) ||
        !write_bytes("checked-reader-empty.tmp", binary, 0)) return 7;
    if (!expect_bytes(rt_file_read_text_at_checked(text("checked-reader-ascii.tmp"), 0, 99), ascii, 6)) return 8;
    if (!expect_bytes(rt_file_read_text_at_checked(text("checked-reader-ascii.tmp"), 2, 3), ascii + 2, 3)) return 9;
    if (!expect_bytes(rt_file_read_text_at_checked(text("checked-reader-binary.tmp"), 0, 99), binary, sizeof(binary))) return 10;
    if (!expect_bytes(rt_file_read_text_at_checked(text("checked-reader-binary.tmp"), 1, 4), binary + 1, 4)) return 11;
    if (!expect_bytes(rt_file_read_text_at_checked(text("checked-reader-empty.tmp"), 0, 99), NULL, 0)) return 12;
    if (!expect_bytes(rt_file_read_text_at_checked(text("checked-reader-ascii.tmp"), 6, 99), NULL, 0)) return 13;
    if (!expect_bytes(rt_file_read_text_at_checked(text("checked-reader-ascii.tmp"), INT64_MAX, 1), NULL, 0)) return 14;
    if (!expect_bytes(rt_file_read_text_at_checked(text("checked-reader-never-exists.tmp"), 0, 0), NULL, 0)) return 15;
    if (!expect_nil(rt_file_read_text_at_checked(text("checked-reader-never-exists.tmp"), 0, 99))) return 16;
    if (!expect_nil(rt_file_read_text_at_checked(text("checked-reader-ascii.tmp"), -1, 1))) return 17;
    if (!expect_nil(rt_file_read_text_at_checked(text("checked-reader-ascii.tmp"), 0, -1))) return 18;
    if (!expect_nil(rt_file_read_text_at_checked(0, 0, 1))) return 19;
    if (!expect_nil(rt_file_read_text_at_checked(rt_value_nil(), 0, 1))) return 20;
    if (!expect_nil(rt_file_read_text_at_checked(text("\xff"), 0, 1))) return 21;
    if (!expect_nil(rt_file_read_text_at_checked(text("."), 0, 1))) return 22;
    if (remove("checked-reader-ascii.tmp") || remove("checked-reader-binary.tmp") || remove("checked-reader-empty.tmp")) return 23;
    printf("CORE_CHECKED_READER_PASS checks=%d unicode_fixture_bytes=%zu\n", checks, size);
    return 0;
}
