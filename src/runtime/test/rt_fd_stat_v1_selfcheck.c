#include "../runtime_fd_stat_v1.h"

#include <assert.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>

#if !defined(_WIN32)
#include <unistd.h>

static void write_exact(int fd, const char *value, size_t size) {
    assert(write(fd, value, size) == (ssize_t)size);
}

int main(void) {
    char directory[] = "/tmp/simple-fd-stat-v1-XXXXXX";
    char original[256];
    char replacement[256];
    uint64_t first[RT_FD_STAT_V1_WORDS];
    uint64_t still_first[RT_FD_STAT_V1_WORDS];
    uint64_t second[RT_FD_STAT_V1_WORDS];
    uint64_t rejected[RT_FD_STAT_V1_WORDS];

    assert(mkdtemp(directory) != NULL);
    assert(snprintf(original, sizeof(original), "%s/artifact", directory) > 0);
    assert(snprintf(replacement, sizeof(replacement), "%s/new", directory) > 0);

    int old_fd = open(original, O_CREAT | O_EXCL | O_RDWR | O_CLOEXEC, 0600);
    assert(old_fd >= 0);
    write_exact(old_fd, "old", 3);
    assert(rt_fd_stat_snapshot_v1_impl(old_fd, first, RT_FD_STAT_V1_BYTES) == 0);
    assert(first[3] == 3 && first[9] == RT_FD_STAT_KIND_V1_REGULAR);

    int new_fd = open(replacement, O_CREAT | O_EXCL | O_RDWR | O_CLOEXEC, 0600);
    assert(new_fd >= 0);
    write_exact(new_fd, "replacement", 11);
    assert(rename(replacement, original) == 0);

    assert(rt_fd_stat_snapshot_v1_impl(old_fd, still_first, RT_FD_STAT_V1_BYTES) == 0);
    assert(still_first[3] == 3);
    assert(still_first[0] == first[0] && still_first[1] == first[1]);

    int reopened_fd = open(original, O_RDONLY | O_CLOEXEC);
    assert(reopened_fd >= 0);
    assert(rt_fd_stat_snapshot_v1_impl(reopened_fd, second, RT_FD_STAT_V1_BYTES) == 0);
    assert(second[3] == 11);
    assert(second[0] != first[0] || second[1] != first[1] || second[2] != first[2]);

    for (int i = 0; i < RT_FD_STAT_V1_WORDS; ++i) rejected[i] = UINT64_MAX;
    assert(rt_fd_stat_snapshot_v1_impl(-1, rejected, RT_FD_STAT_V1_BYTES) < 0);
    for (int i = 0; i < RT_FD_STAT_V1_WORDS; ++i) assert(rejected[i] == 0);
    assert(rt_fd_stat_snapshot_v1_impl(old_fd, rejected, RT_FD_STAT_V1_BYTES - 1) == -EINVAL);

    assert(ftruncate(old_fd, 1) == 0);
    assert(rt_fd_stat_snapshot_v1_impl(old_fd, still_first, RT_FD_STAT_V1_BYTES) == 0);
    assert(still_first[3] == 1);

    assert(close(reopened_fd) == 0);
    assert(close(new_fd) == 0);
    assert(close(old_fd) == 0);
    assert(unlink(original) == 0);
    assert(rmdir(directory) == 0);
    puts("rt_fd_stat_v1_selfcheck: PASS");
    return 0;
}
#else
int main(void) {
    char path[MAX_PATH];
    char directory[MAX_PATH];
    DWORD written = 0;
    uint64_t observed[RT_FD_STAT_V1_WORDS];
    assert(GetTempPathA(MAX_PATH, directory) > 0);
    assert(GetTempFileNameA(directory, "sfd", 0, path) != 0);
    HANDLE handle = CreateFileA(path, GENERIC_READ | GENERIC_WRITE, 0, NULL,
        OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    assert(handle != INVALID_HANDLE_VALUE);
    assert(WriteFile(handle, "windows", 7, &written, NULL) && written == 7);
    int fd = _open_osfhandle((intptr_t)handle, _O_BINARY | _O_RDONLY);
    assert(fd >= 0);
#if defined(_MSC_VER)
    assert(rt_fd_stat_snapshot_v1_impl(fd, observed, RT_FD_STAT_V1_BYTES) == 0);
    assert(observed[3] == 7 && observed[9] == RT_FD_STAT_KIND_V1_REGULAR);
    assert(observed[1] != 0 || observed[2] != 0);
    assert(_close(fd) == 0);
    assert(rt_fd_stat_snapshot_v1_impl(fd, observed, RT_FD_STAT_V1_BYTES) == -EBADF);
#else
    assert(rt_fd_stat_snapshot_v1_impl(fd, observed, RT_FD_STAT_V1_BYTES) == -ENOTSUP);
    assert(_close(fd) == 0);
#endif
    assert(DeleteFileA(path));
    puts("rt_fd_stat_v1_selfcheck: PASS");
    return 0;
}
#endif
