#define _GNU_SOURCE
#include "runtime.h"
#include "runtime_thread.h"
#include <assert.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static void check_read(const char *path, int64_t bound, const char *expected) {
    int64_t value = rt_shared_parse_cell_read_v1((const uint8_t *)path, strlen(path), bound);
    assert(rt_string_len(value) == (int64_t)strlen(expected));
    assert(memcmp(rt_string_data(value), expected, strlen(expected)) == 0);
    rt_string_free(value);
}

int main(void) {
    char directory[] = "/tmp/simple-provider-check.XXXXXX";
    assert(mkdtemp(directory));
    char file[256], alias[256], dir_alias[256];
    snprintf(file, sizeof(file), "%s/cell", directory);
    snprintf(alias, sizeof(alias), "%s/cell-link", directory);
    snprintf(dir_alias, sizeof(dir_alias), "%s-link", directory);
    FILE *stream = fopen(file, "wb");
    assert(stream);
    assert(fwrite("real cache payload", 1, 18, stream) == 18);
    assert(fclose(stream) == 0);
    assert(symlink(file, alias) == 0);
    assert(symlink(directory, dir_alias) == 0);
    assert(rt_dir_is_real_no_follow((const uint8_t *)directory, strlen(directory)) == 1);
    assert(rt_dir_is_real_no_follow((const uint8_t *)dir_alias, strlen(dir_alias)) == 0);
    assert(rt_dir_is_real_no_follow((const uint8_t *)file, strlen(file)) == 0);
    assert(spl_thread_current_id() == (int64_t)pthread_self());
    check_read(file, 1024, "real cache payload");
    check_read(file, 4, "");
    check_read(alias, 1024, "");
    check_read(directory, 1024, "");
    check_read(file, 0, "");
    assert(unlink(file) == 0);
    check_read(file, 1024, "");
    assert(unlink(alias) == 0);
    assert(unlink(dir_alias) == 0);
    assert(rmdir(directory) == 0);
    puts("PASS: real directory, bounded nofollow reads, string owner/free, native thread id");
    return 0;
}
