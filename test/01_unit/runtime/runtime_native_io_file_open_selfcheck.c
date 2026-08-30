#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

int64_t rt_io_file_open(const uint8_t *path_ptr, uint64_t path_len, int64_t mode);

int main(void) {
    char path[256];
    const char payload[] = "simple-io-abi";
    char actual[sizeof(payload)] = {0};
    int fd;

    snprintf(path, sizeof(path), "/tmp/simple-io-open-%ld.tmp", (long)getpid());
    unlink(path);

    fd = (int)rt_io_file_open((const uint8_t *)path, strlen(path), 1);
    if (fd < 0 || write(fd, payload, sizeof(payload)) != (ssize_t)sizeof(payload)) return 1;
    if (close(fd) != 0) return 2;

    fd = (int)rt_io_file_open((const uint8_t *)path, strlen(path), 0);
    if (fd < 0 || read(fd, actual, sizeof(actual)) != (ssize_t)sizeof(actual)) return 3;
    if (close(fd) != 0 || memcmp(actual, payload, sizeof(payload)) != 0) return 4;

    unlink(path);
    if (rt_io_file_open((const uint8_t *)path, strlen(path), 0) != -1) return 5;
    if (rt_io_file_open((const uint8_t *)path, strlen(path), 99) != -1) return 6;
    if (rt_io_file_open(NULL, 1, 0) != -1) return 7;
    return 0;
}
