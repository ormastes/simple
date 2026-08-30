#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

int64_t rt_file_mmap_read_text(const uint8_t *path_ptr, uint64_t path_len);
int64_t rt_string_len(int64_t value);
const uint8_t *rt_string_data(int64_t value);

int main(void) {
    const char *path = "/tmp/simple-runtime-mmap-text.tmp";
    const char payload[] = "mapped text\nwith utf8: \xcf\x80";
    FILE *file = fopen(path, "wb");
    if (!file) return 1;
    if (fwrite(payload, 1, sizeof(payload) - 1, file) != sizeof(payload) - 1) return 2;
    if (fclose(file) != 0) return 3;
    int64_t text = rt_file_mmap_read_text((const uint8_t *)path, strlen(path));
    if (rt_string_len(text) != (int64_t)sizeof(payload) - 1) return 4;
    if (memcmp(rt_string_data(text), payload, sizeof(payload) - 1) != 0) return 5;
    unlink(path);
    if (rt_file_mmap_read_text((const uint8_t *)path, strlen(path)) != 3) return 6;
    if (rt_file_mmap_read_text(NULL, 1) != 3) return 7;
    file = fopen(path, "wb");
    if (!file || fclose(file) != 0) return 8;
    if (rt_file_mmap_read_text((const uint8_t *)path, strlen(path)) != 3) return 9;
    unlink(path);
    puts("PASS runtime mmap text ABI");
    return 0;
}
