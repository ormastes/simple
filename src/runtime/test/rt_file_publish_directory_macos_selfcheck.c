#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

int64_t rt_file_publish_noreplace(const uint8_t *staged, uint64_t staged_len,
                                  const uint8_t *destination, uint64_t destination_len);

static int64_t publish(const char *from, const char *to) {
    return rt_file_publish_noreplace((const uint8_t *)from, strlen(from),
                                     (const uint8_t *)to, strlen(to));
}

static void path(char *out, size_t capacity, const char *root, const char *leaf) {
    int n = snprintf(out, capacity, "%s/%s", root, leaf);
    assert(n > 0 && (size_t)n < capacity);
}

int main(void) {
    char root[] = "/tmp/simple-publish-dir-XXXXXX";
    assert(mkdtemp(root));
    char staged[256], destination[256], other[256], dangling[256],
         target[256], marker[256];
    path(staged, sizeof(staged), root, "staged");
    path(destination, sizeof(destination), root, "outputs");
    path(other, sizeof(other), root, "other");
    path(dangling, sizeof(dangling), root, "dangling");
    path(target, sizeof(target), root, "missing-target");
    assert(mkdir(staged, 0700) == 0);
    assert(publish(staged, destination) == 1);
    struct stat st;
    assert(lstat(destination, &st) == 0 && S_ISDIR(st.st_mode));
    assert(lstat(staged, &st) != 0);

    assert(mkdir(other, 0700) == 0);
    assert(publish(other, destination) == 0);
    assert(lstat(other, &st) == 0 && S_ISDIR(st.st_mode));
    assert(lstat(destination, &st) == 0 && S_ISDIR(st.st_mode));

    assert(symlink(target, dangling) == 0);
    assert(publish(other, dangling) == 0);
    assert(lstat(dangling, &st) == 0 && S_ISLNK(st.st_mode));
    assert(lstat(other, &st) == 0 && S_ISDIR(st.st_mode));

    path(marker, sizeof(marker), destination, "kept");
    FILE *file = fopen(marker, "wb");
    assert(file);
    assert(fwrite("ok", 1, 2, file) == 2);
    assert(fclose(file) == 0);
    assert(publish(other, destination) == 0);
    assert(lstat(marker, &st) == 0 && S_ISREG(st.st_mode));

    assert(unlink(marker) == 0);
    assert(unlink(dangling) == 0);
    assert(rmdir(other) == 0);
    assert(rmdir(destination) == 0);
    assert(rmdir(root) == 0);
    puts("rt_file_publish_directory_macos_selfcheck: PASS");
    return 0;
}
