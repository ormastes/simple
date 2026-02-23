/*
 * Async I/O Driver — Dispatch + FFI Bridge
 *
 * Section A: spl_driver_* public API dispatches through the vtable.
 * Section B: rt_driver_* FFI bridge maps i64 handles to driver pointers
 *            so Simple's FFI (which only passes i64) can use the driver.
 */

#include "platform/async_driver.h"
#include <stdlib.h>
#include <string.h>

/* ================================================================
 * Section A — spl_driver_* dispatch through vtable
 * ================================================================ */

spl_driver* spl_driver_create(int64_t queue_depth) {
    if (queue_depth <= 0) queue_depth = 256;

#if defined(__linux__)
    spl_driver* d = spl_driver_create_uring(queue_depth);
    if (!d) d = spl_driver_create_epoll(queue_depth);
    return d;
#elif defined(__APPLE__) || defined(__FreeBSD__)
    return spl_driver_create_kqueue(queue_depth);
#elif defined(_WIN32)
    return spl_driver_create_iocp(queue_depth);
#else
    (void)queue_depth;
    return NULL;
#endif
}

void spl_driver_destroy(spl_driver* d) {
    if (d && d->vtable) d->vtable->destroy(d);
}

int64_t spl_driver_submit_accept(spl_driver* d, int64_t listen_fd) {
    return d->vtable->submit_accept(d, listen_fd);
}

int64_t spl_driver_submit_connect(spl_driver* d, int64_t fd,
                                   const char* addr, int64_t port) {
    return d->vtable->submit_connect(d, fd, addr, port);
}

int64_t spl_driver_submit_recv(spl_driver* d, int64_t fd, int64_t buf_size) {
    return d->vtable->submit_recv(d, fd, buf_size);
}

int64_t spl_driver_submit_send(spl_driver* d, int64_t fd,
                                const char* data, int64_t len) {
    return d->vtable->submit_send(d, fd, data, len);
}

int64_t spl_driver_submit_sendfile(spl_driver* d, int64_t sock_fd,
                                    int64_t file_fd, int64_t offset,
                                    int64_t len) {
    return d->vtable->submit_sendfile(d, sock_fd, file_fd, offset, len);
}

int64_t spl_driver_submit_read(spl_driver* d, int64_t fd,
                                int64_t buf_size, int64_t offset) {
    return d->vtable->submit_read(d, fd, buf_size, offset);
}

int64_t spl_driver_submit_write(spl_driver* d, int64_t fd,
                                 const char* data, int64_t len,
                                 int64_t offset) {
    return d->vtable->submit_write(d, fd, data, len, offset);
}

int64_t spl_driver_submit_open(spl_driver* d, const char* path,
                                int64_t flags, int64_t mode) {
    return d->vtable->submit_open(d, path, flags, mode);
}

int64_t spl_driver_submit_close(spl_driver* d, int64_t fd) {
    return d->vtable->submit_close(d, fd);
}

int64_t spl_driver_submit_fsync(spl_driver* d, int64_t fd) {
    return d->vtable->submit_fsync(d, fd);
}

int64_t spl_driver_submit_timeout(spl_driver* d, int64_t timeout_ms) {
    return d->vtable->submit_timeout(d, timeout_ms);
}

int64_t spl_driver_flush(spl_driver* d) {
    return d->vtable->flush(d);
}

int64_t spl_driver_poll(spl_driver* d, spl_completion* out, int64_t max,
                         int64_t timeout_ms) {
    return d->vtable->poll(d, out, max, timeout_ms);
}

bool spl_driver_cancel(spl_driver* d, int64_t op_id) {
    return d->vtable->cancel(d, op_id);
}

const char* spl_driver_backend_name(spl_driver* d) {
    return d->vtable->backend_name(d);
}

spl_backend_type spl_driver_backend_type(spl_driver* d) {
    return d->vtable->backend_type_fn(d);
}

bool spl_driver_supports_sendfile(spl_driver* d) {
    return d->vtable->supports_sendfile(d);
}

bool spl_driver_supports_zero_copy(spl_driver* d) {
    return d->vtable->supports_zero_copy(d);
}

/* ================================================================
 * Section B — rt_driver_* FFI bridge (handle table)
 * ================================================================ */

#define MAX_DRIVERS   64
#define MAX_POLL_BUF  4096

static spl_driver*    g_drivers[MAX_DRIVERS];
static spl_completion g_poll_buf[MAX_POLL_BUF];
static int64_t        g_poll_count = 0;

/* --- handle helpers ---------------------------------------------------- */

static int64_t alloc_handle(spl_driver* d) {
    for (int64_t i = 0; i < MAX_DRIVERS; i++) {
        if (!g_drivers[i]) {
            g_drivers[i] = d;
            return i;
        }
    }
    return -1;
}

static spl_driver* get_driver(int64_t handle) {
    if (handle < 0 || handle >= MAX_DRIVERS) return NULL;
    return g_drivers[handle];
}

static void free_handle(int64_t handle) {
    if (handle >= 0 && handle < MAX_DRIVERS)
        g_drivers[handle] = NULL;
}

/* --- rt_driver_* bridge functions -------------------------------------- */

int64_t rt_driver_create(int64_t queue_depth) {
    spl_driver* d = spl_driver_create(queue_depth);
    if (!d) return -1;
    int64_t h = alloc_handle(d);
    if (h < 0) {
        spl_driver_destroy(d);
        return -1;
    }
    return h;
}

void rt_driver_destroy(int64_t handle) {
    spl_driver* d = get_driver(handle);
    if (d) {
        spl_driver_destroy(d);
        free_handle(handle);
    }
}

int64_t rt_driver_submit_accept(int64_t handle, int64_t listen_fd) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_submit_accept(d, listen_fd);
}

int64_t rt_driver_submit_connect(int64_t handle, int64_t fd,
                                  const char* addr, int64_t port) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_submit_connect(d, fd, addr, port);
}

int64_t rt_driver_submit_recv(int64_t handle, int64_t fd, int64_t buf_size) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_submit_recv(d, fd, buf_size);
}

int64_t rt_driver_submit_send(int64_t handle, int64_t fd,
                               const char* data, int64_t len) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_submit_send(d, fd, data, len);
}

int64_t rt_driver_submit_sendfile(int64_t handle, int64_t sock_fd,
                                   int64_t file_fd, int64_t offset,
                                   int64_t len) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_submit_sendfile(d, sock_fd, file_fd, offset, len);
}

int64_t rt_driver_submit_read(int64_t handle, int64_t fd,
                               int64_t buf_size, int64_t offset) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_submit_read(d, fd, buf_size, offset);
}

int64_t rt_driver_submit_write(int64_t handle, int64_t fd,
                                const char* data, int64_t len,
                                int64_t offset) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_submit_write(d, fd, data, len, offset);
}

int64_t rt_driver_submit_open(int64_t handle, const char* path,
                               int64_t flags, int64_t mode) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_submit_open(d, path, flags, mode);
}

int64_t rt_driver_submit_close(int64_t handle, int64_t fd) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_submit_close(d, fd);
}

int64_t rt_driver_submit_fsync(int64_t handle, int64_t fd) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_submit_fsync(d, fd);
}

int64_t rt_driver_submit_timeout(int64_t handle, int64_t timeout_ms) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_submit_timeout(d, timeout_ms);
}

int64_t rt_driver_flush(int64_t handle) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    return spl_driver_flush(d);
}

int64_t rt_driver_poll(int64_t handle, int64_t max, int64_t timeout_ms) {
    spl_driver* d = get_driver(handle);
    if (!d) return -1;
    if (max > MAX_POLL_BUF) max = MAX_POLL_BUF;
    g_poll_count = spl_driver_poll(d, g_poll_buf, max, timeout_ms);
    return g_poll_count;
}

int64_t rt_driver_poll_id(int64_t handle, int64_t index) {
    (void)handle;
    if (index < 0 || index >= g_poll_count) return -1;
    return g_poll_buf[index].id;
}

int64_t rt_driver_poll_result(int64_t handle, int64_t index) {
    (void)handle;
    if (index < 0 || index >= g_poll_count) return -1;
    return g_poll_buf[index].result;
}

int64_t rt_driver_poll_flags(int64_t handle, int64_t index) {
    (void)handle;
    if (index < 0 || index >= g_poll_count) return 0;
    return g_poll_buf[index].flags;
}

bool rt_driver_cancel(int64_t handle, int64_t op_id) {
    spl_driver* d = get_driver(handle);
    if (!d) return false;
    return spl_driver_cancel(d, op_id);
}

const char* rt_driver_backend_name(int64_t handle) {
    spl_driver* d = get_driver(handle);
    if (!d) return "none";
    return spl_driver_backend_name(d);
}

bool rt_driver_supports_sendfile(int64_t handle) {
    spl_driver* d = get_driver(handle);
    if (!d) return false;
    return spl_driver_supports_sendfile(d);
}

bool rt_driver_supports_zero_copy(int64_t handle) {
    spl_driver* d = get_driver(handle);
    if (!d) return false;
    return spl_driver_supports_zero_copy(d);
}
