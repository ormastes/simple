#define _POSIX_C_SOURCE 200809L
#include "../runtime.h"

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

static int write_fixture(const char* path, const char* content) {
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0600);
    if (fd < 0) return 0;
    size_t length = strlen(content);
    ssize_t written = write(fd, content, length);
    return close(fd) == 0 && written == (ssize_t)length;
}

static int content_equals(const char* path, const char* expected) {
    char buffer[128];
    int fd = open(path, O_RDONLY);
    if (fd < 0) return 0;
    ssize_t count = read(fd, buffer, sizeof(buffer));
    int closed = close(fd);
    size_t expected_length = strlen(expected);
    return closed == 0 && count == (ssize_t)expected_length &&
        memcmp(buffer, expected, expected_length) == 0;
}

int main(void) {
    char root[PATH_MAX];
    if (snprintf(root, sizeof(root), "/tmp/simple-m3-publication.%ld",
            (long)getpid()) < 0) return 10;
    if (mkdir(root, 0700) != 0) return 10;

    char source[PATH_MAX];
    char staging[PATH_MAX];
    char final_path[PATH_MAX];
    char conflict_source[PATH_MAX];
    char conflict_staging[PATH_MAX];
    char source_link[PATH_MAX];
    char rejected_staging[PATH_MAX];
    if (snprintf(source, sizeof(source), "%s/source.o", root) < 0 ||
        snprintf(staging, sizeof(staging), "%s/staging.o", root) < 0 ||
        snprintf(final_path, sizeof(final_path), "%s/final.o", root) < 0 ||
        snprintf(conflict_source, sizeof(conflict_source), "%s/conflict-source.o", root) < 0 ||
        snprintf(conflict_staging, sizeof(conflict_staging), "%s/conflict-staging.o", root) < 0 ||
        snprintf(source_link, sizeof(source_link), "%s/source-link.o", root) < 0 ||
        snprintf(rejected_staging, sizeof(rejected_staging), "%s/rejected.o", root) < 0) return 11;

    const char* admitted = "complete-object-bytes";
    const char* conflicting = "conflicting-object-bytes";
    if (!write_fixture(source, admitted)) return 12;
    if (!rt_file_copy_create_excl_no_follow(
            source, (int64_t)strlen(source),
            staging, (int64_t)strlen(staging))) return 13;

    /* Simulated interruption boundary: staging is complete, but the final
     * name has never existed and therefore cannot expose empty/partial bytes. */
    if (!content_equals(staging, admitted)) return 14;
    if (access(final_path, F_OK) == 0 || errno != ENOENT) return 15;

    if (!rt_file_link_create_excl_no_follow(
            staging, (int64_t)strlen(staging),
            final_path, (int64_t)strlen(final_path))) return 16;
    if (!content_equals(final_path, admitted)) return 17;

    if (!write_fixture(conflict_source, conflicting)) return 18;
    if (!rt_file_copy_create_excl_no_follow(
            conflict_source, (int64_t)strlen(conflict_source),
            conflict_staging, (int64_t)strlen(conflict_staging))) return 19;
    if (rt_file_link_create_excl_no_follow(
            conflict_staging, (int64_t)strlen(conflict_staging),
            final_path, (int64_t)strlen(final_path))) return 20;
    if (!content_equals(final_path, admitted)) return 21;

    if (symlink(source, source_link) != 0) return 22;
    if (rt_file_copy_create_excl_no_follow(
            source_link, (int64_t)strlen(source_link),
            rejected_staging, (int64_t)strlen(rejected_staging))) return 23;
    if (access(rejected_staging, F_OK) == 0 || errno != ENOENT) return 24;

    unlink(source_link);
    unlink(conflict_staging);
    unlink(conflict_source);
    unlink(final_path);
    unlink(staging);
    unlink(source);
    if (rmdir(root) != 0) return 25;
    return 0;
}
