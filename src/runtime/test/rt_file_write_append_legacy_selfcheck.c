/* Covers legacy rt_file_write / rt_file_append (shared write-mode helper). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int rt_file_write(const char* path, const char* content);
extern int rt_file_append(const char* path, const char* content);

#define CHECK(c) do { if (!(c)) { printf("FAIL line %d: %s\n", __LINE__, #c); return 1; } } while (0)

static int slurp(const char* path, char* buf, size_t cap) {
    FILE* f = fopen(path, "rb");
    if (!f) return -1;
    size_t n = fread(buf, 1, cap - 1, f);
    fclose(f);
    buf[n] = '\0';
    return (int)n;
}

int main(void) {
    char path[512];
    const char* dir = getenv("TMPDIR");
    if (!dir) dir = getenv("TEMP");
    if (!dir) dir = ".";
    snprintf(path, sizeof(path), "%s/rt_file_write_append_legacy_selfcheck.%d.tmp", dir, (int)rand());
    char buf[64];
    CHECK(rt_file_write(path, "hello") == 1);
    CHECK(slurp(path, buf, sizeof(buf)) == 5 && strcmp(buf, "hello") == 0);
    CHECK(rt_file_append(path, " world") == 1);
    CHECK(slurp(path, buf, sizeof(buf)) == 11 && strcmp(buf, "hello world") == 0);
    CHECK(rt_file_append(path, NULL) == 1);
    CHECK(rt_file_write(path, NULL) == 1);
    CHECK(slurp(path, buf, sizeof(buf)) == 0);
    CHECK(rt_file_write(NULL, "x") == 0);
    CHECK(rt_file_append(NULL, "x") == 0);
    remove(path);
    printf("PASS rt_file_write_append_legacy\n");
    return 0;
}
