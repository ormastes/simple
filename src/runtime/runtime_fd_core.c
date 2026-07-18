#include "runtime.h"

#if defined(_WIN32)
int64_t rt_unix_socket_connect(const char* path) {
    (void)path;
    return -1;
}

int64_t rt_fd_write(int64_t fd, const char* data, int64_t len) {
    (void)fd;
    (void)data;
    (void)len;
    return -1;
}

const char* rt_fd_read_until(int64_t fd, uint8_t stop_byte, int64_t max) {
    (void)fd;
    (void)stop_byte;
    (void)max;
    return "";
}

bool rt_fd_close(int64_t fd) {
    (void)fd;
    return false;
}
#else
#include "platform/unix_fd.h"
#endif
