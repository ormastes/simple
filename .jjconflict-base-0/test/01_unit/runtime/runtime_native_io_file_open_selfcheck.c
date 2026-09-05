#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

int64_t rt_io_file_open(const uint8_t *path_ptr, uint64_t path_len, int64_t mode);
_Bool rt_io_file_close(int64_t fd);
int64_t rt_io_file_read_all(int64_t fd);
int64_t rt_array_len(void *array);
int64_t rt_bytes_u8_at(void *array, int64_t index);

int main(void) {
    char path[256];
    const char payload[] = "simple-io-abi";
    char actual[sizeof(payload)] = {0};
    int fd;

    snprintf(path, sizeof(path), "/tmp/simple-io-open-%ld.tmp", (long)getpid());
    unlink(path);

    fd = (int)rt_io_file_open((const uint8_t *)path, strlen(path), 1);
    if (fd < 0 || write(fd, payload, sizeof(payload)) != (ssize_t)sizeof(payload)) return 1;
    if (!rt_io_file_close(fd)) return 2;

    fd = (int)rt_io_file_open((const uint8_t *)path, strlen(path), 0);
    if (fd < 0) return 3;
    int64_t bytes = rt_io_file_read_all(fd);
    if (rt_array_len((void *)(uintptr_t)bytes) != (int64_t)sizeof(payload)) return 4;
    for (size_t i = 0; i < sizeof(payload); i++) {
        actual[i] = (char)rt_bytes_u8_at((void *)(uintptr_t)bytes, (int64_t)i);
    }
    if (!rt_io_file_close(fd) || memcmp(actual, payload, sizeof(payload)) != 0) return 5;

    unlink(path);
    if (rt_io_file_open((const uint8_t *)path, strlen(path), 0) != -1) return 6;
    if (rt_io_file_open((const uint8_t *)path, strlen(path), 99) != -1) return 7;
    if (rt_io_file_open(NULL, 1, 0) != -1) return 8;
    if (rt_io_file_close(-1)) return 9;
    if (rt_io_file_read_all(-1) != 3) return 10;
    return 0;
}
