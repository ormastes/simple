#include "../runtime.h"

#include <assert.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

typedef struct { const uint8_t *data; int64_t len; } TestText;

const uint8_t *rt_string_data(int64_t value) { return ((TestText *)(uintptr_t)value)->data; }
int64_t rt_string_len(int64_t value) { return ((TestText *)(uintptr_t)value)->len; }

SplArray *rt_array_new(int64_t cap) {
    SplArray *a = calloc(1, sizeof(*a));
    if (!a) return NULL;
    a->cap = cap;
    a->items = cap ? calloc((size_t)cap, sizeof(*a->items)) : NULL;
    if (cap && !a->items) { free(a); return NULL; }
    return a;
}

void rt_array_free(SplArray *a) { if (a) { free(a->items); free(a); } }

int8_t rt_array_push(SplArray *a, int64_t value) {
    if (!a || a->len >= a->cap) return 0;
    a->items[a->len++].as_int = value;
    return 1;
}

static TestText text(const char *value) {
    TestText result = {(const uint8_t *)value, (int64_t)strlen(value)};
    return result;
}

int main(void) {
    char root[] = "/tmp/simple-file-view-XXXXXX";
    assert(mkdtemp(root));
    char nested[256], file[512], link_path[512];
    snprintf(nested, sizeof(nested), "%s/nested", root);
    snprintf(file, sizeof(file), "%s/data.bin", nested);
    snprintf(link_path, sizeof(link_path), "%s/link.bin", nested);
    assert(mkdir(nested, 0700) == 0);
    int fd = open(file, O_CREAT | O_EXCL | O_WRONLY, 0600);
    assert(fd >= 0);
    assert(write(fd, "abcdef", 6) == 6);
    assert(close(fd) == 0);
    assert(symlink("data.bin", link_path) == 0);

    TestText root_text = text(root), path_text = text("nested/data.bin");
    int64_t handle = rt_file_view_open_beneath_no_follow_v1(
        (int64_t)(uintptr_t)&root_text, (int64_t)(uintptr_t)&path_text);
    assert(handle > 0);
    assert(rt_file_view_size_v1(handle) == 6);
    assert(rt_file_view_device_v1(handle) >= 0);
    assert(rt_file_view_inode_v1(handle) >= 0);

    SplArray *bytes = (SplArray *)(uintptr_t)rt_file_view_pread_exact_v1(handle, 1, 3);
    assert(bytes && bytes->len == 3);
    assert((bytes->items[0].as_int >> 3) == 'b');
    assert((bytes->items[1].as_int >> 3) == 'c');
    assert((bytes->items[2].as_int >> 3) == 'd');
    rt_array_free(bytes);
    assert(rt_file_view_pread_exact_v1(handle, 5, 2) == 0);
    assert(rt_file_view_close_v1(handle));
    assert(!rt_file_view_close_v1(handle));

    TestText link_text = text("nested/link.bin");
    assert(rt_file_view_open_beneath_no_follow_v1(
        (int64_t)(uintptr_t)&root_text, (int64_t)(uintptr_t)&link_text) == -3);
    TestText escape_text = text("../data.bin");
    assert(rt_file_view_open_beneath_no_follow_v1(
        (int64_t)(uintptr_t)&root_text, (int64_t)(uintptr_t)&escape_text) == -2);

    assert(unlink(link_path) == 0);
    assert(unlink(file) == 0);
    assert(rmdir(nested) == 0);
    assert(rmdir(root) == 0);
    puts("rt_file_view_selfcheck: PASS");
    return 0;
}
