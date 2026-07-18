#ifndef SPL_UNIX_FD_H
#define SPL_UNIX_FD_H

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>

int64_t rt_unix_socket_connect(const char* path) {
    if (!path) return -1;

    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd < 0) return -1;

    struct sockaddr_un addr;
    memset(&addr, 0, sizeof(addr));
    addr.sun_family = AF_UNIX;
    strncpy(addr.sun_path, path, sizeof(addr.sun_path) - 1);

    if (connect(fd, (struct sockaddr*)&addr, sizeof(addr)) != 0) {
        close(fd);
        return -1;
    }
    return (int64_t)fd;
}

int64_t rt_fd_write(int64_t fd, const char* data, int64_t len) {
    if (fd < 0 || !data || len <= 0) return -1;
    ssize_t n = write((int)fd, data, (size_t)len);
    return (int64_t)n;
}

/* Successful buffers follow the runtime-owned borrowed-text convention. */
const char* rt_fd_read_until(int64_t fd, uint8_t stop_byte, int64_t max) {
    if (fd < 0 || max <= 0) return "";

    char* buf = (char*)malloc((size_t)max + 1);
    if (!buf) return "";

    int64_t total = 0;
    while (total < max) {
        ssize_t n = read((int)fd, buf + total, 1);
        if (n <= 0) break;
        total++;
        if ((uint8_t)buf[total - 1] == stop_byte) break;
    }
    buf[total] = '\0';
    return buf;
}

bool rt_fd_close(int64_t fd) {
    if (fd < 0) return false;
    return close((int)fd) == 0;
}

#endif
