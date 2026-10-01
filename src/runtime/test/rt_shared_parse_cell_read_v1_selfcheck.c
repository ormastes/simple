/* Bounded host-provider selfcheck; link with runtime_secure_staging.c and
 * --gc-sections so unrelated runtime imports remain outside this fixture. */
#include "runtime.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifndef _WIN32
#include <unistd.h>
#endif

int64_t rt_shared_parse_cell_read_v1(const uint8_t *, uint64_t, int64_t);

static uint64_t observed_size;
static uint8_t observed_bytes[32];

int64_t rt_string_new(const uint8_t *bytes, uint64_t size) {
    observed_size = size;
    memset(observed_bytes, 0, sizeof observed_bytes);
    if (bytes && size <= sizeof observed_bytes)
        memcpy(observed_bytes, bytes, (size_t)size);
    return 1;
}

static int read_expect(const char *path, int64_t max, uint64_t size) {
    observed_size = UINT64_MAX;
    (void)rt_shared_parse_cell_read_v1((const uint8_t *)path,
                                      (uint64_t)strlen(path), max);
    return observed_size == size;
}

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    const char *path = argv[1];
    FILE *file = fopen(path, "wb");
    if (!file || fwrite("hello", 1, 5, file) != 5 || fclose(file)) return 3;
    if (!read_expect(path, 5, 5) || memcmp(observed_bytes, "hello", 5) != 0)
        return 4;
    if (!read_expect(path, 4, 0)) return 5;
#ifndef _WIN32
    char link_path[4096];
    if (snprintf(link_path, sizeof link_path, "%s.link", path) <= 0 ||
        symlink(path, link_path) != 0) return 6;
    if (!read_expect(link_path, 5, 0)) return 7;
    unlink(link_path);
#endif
    if (remove(path) != 0 || !read_expect(path, 5, 0)) return 8;
    return 0;
}
