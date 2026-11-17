/* Covers rt_file_read_text (ptr,len) and rt_file_read_text_rv (RuntimeValue
 * path): both must read a whole file (> one 4096-byte chunk, to exercise the
 * grow path) and return nil for a missing file. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int64_t rt_file_read_text(const uint8_t* path_ptr, uint64_t path_len);
extern int64_t rt_file_read_text_rv(int64_t path_value);
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_len(int64_t value);

#define CHECK(c) do { if (!(c)) { printf("FAIL line %d: %s\n", __LINE__, #c); return 1; } } while (0)

int main(void) {
    char path[512];
    const char* dir = getenv("TMPDIR");
    if (!dir) dir = getenv("TEMP");
    if (!dir) dir = ".";
    snprintf(path, sizeof(path), "%s/rt_file_read_text_native_selfcheck.%d.tmp", dir, (int)rand());
    enum { SIZE = 10000 };
    FILE* f = fopen(path, "wb");
    CHECK(f);
    for (int i = 0; i < SIZE; i++) fputc('a' + (i % 26), f);
    fclose(f);

    int64_t r1 = rt_file_read_text((const uint8_t*)path, strlen(path));
    CHECK(r1 != 3);
    CHECK(rt_string_len(r1) == SIZE);
    int64_t pv = rt_string_new((const uint8_t*)path, strlen(path));
    int64_t r2 = rt_file_read_text_rv(pv);
    CHECK(r2 != 3);
    CHECK(rt_string_len(r2) == SIZE);

    remove(path);
    const char* missing = "/nonexistent_dir_selfcheck/none.txt";
    CHECK(rt_file_read_text((const uint8_t*)missing, strlen(missing)) == 3);
    CHECK(rt_file_read_text_rv(rt_string_new((const uint8_t*)missing, strlen(missing))) == 3);
    printf("PASS rt_file_read_text_native\n");
    return 0;
}
