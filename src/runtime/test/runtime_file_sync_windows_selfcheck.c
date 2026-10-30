/* Real legacy-core provider regression; link the production runtime owners. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <windows.h>

extern int rt_file_sync(const uint8_t *, uint64_t);

static int check_file(const char *root, const char *leaf, size_t count) {
    char path[1024];
    if (snprintf(path, sizeof(path), "%s/%s", root, leaf) >= (int)sizeof(path)) return 1;
    FILE *f = fopen(path, "wbx");
    if (!f) return 2;
    unsigned char block[4096];
    for (size_t i = 0; i < sizeof(block); ++i) block[i] = (unsigned char)(i * 37u);
    for (size_t offset = 0; offset < count;) {
        size_t n = count - offset;
        if (n > sizeof(block)) n = sizeof(block);
        if (fwrite(block, 1, n, f) != n) { fclose(f); return 3; }
        offset += n;
    }
    if (fclose(f)) return 4;
    if (rt_file_sync((const uint8_t *)path, strlen(path)) != 1) return 5;
    f = fopen(path, "rb");
    if (!f) return 6;
    unsigned char actual[4096];
    for (size_t offset = 0; offset < count;) {
        size_t n = count - offset;
        if (n > sizeof(actual)) n = sizeof(actual);
        if (fread(actual, 1, n, f) != n || memcmp(actual, block, n)) { fclose(f); return 7; }
        offset += n;
    }
    int extra = fgetc(f);
    int read_error = ferror(f);
    int close_error = fclose(f);
    if (extra != EOF || read_error || close_error) return 8;
    if (!SetFileAttributesA(path, FILE_ATTRIBUTE_READONLY)) return 9;
    int refused = rt_file_sync((const uint8_t *)path, strlen(path)) == 0;
    if (!SetFileAttributesA(path, FILE_ATTRIBUTE_NORMAL)) return 10;
    if (!refused) return 11;
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 2) return 64;
    /* Refuse to reuse another invocation's directory or files. */
    if (!CreateDirectoryA(argv[1], NULL)) return 65;
    const size_t sizes[] = {0, 18, 8235828};
    const char *names[] = {"empty.bin", "small.bin", "inventory-sized.bin"};
    for (size_t i = 0; i < 3; ++i) {
        int result = check_file(argv[1], names[i], sizes[i]);
        if (result) { fprintf(stderr, "file_sync case=%s failure=%d\n", names[i], result); return result; }
    }
    char missing[1024];
    if (snprintf(missing, sizeof(missing), "%s/missing.bin", argv[1]) >= (int)sizeof(missing)) return 66;
    if (rt_file_sync((const uint8_t *)missing, strlen(missing)) != 0) return 67;
    if (GetFileAttributesA(missing) != INVALID_FILE_ATTRIBUTES) return 68;
    if (rt_file_sync((const uint8_t *)argv[1], strlen(argv[1])) != 0) return 69;
    if (rt_file_sync(NULL, 0) != 0) return 70;
    puts("PASS: existing empty/small/large files synchronized without byte changes; missing, read-only and directory inputs refused");
    return 0;
}
