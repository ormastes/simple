/*
 * Async I/O Driver — Dispatch Layer + Simple FFI Bridge
 *
 * Two API surfaces:
 * 1. spl_driver_* — C vtable dispatch (for C callers and backends)
 * 2. rt_driver_*  — flat handle-based API (for Simple extern fn binding)
 *
 * The rt_driver_* functions use a handle table so Simple code works with
 * integer handles instead of opaque pointers.
 *
 * Thread safety: The handle table uses no locking. In the thread-per-core
 * model each worker creates its own driver on its own thread during startup.
 * If concurrent creation is ever needed, wrap rt_driver_create in a mutex.
 */

#include "async_driver.h"
#include <stdlib.h>
#include <string.h>
#include <errno.h>

/* ===== Handle Table ===== */

#define RT_MAX_DRIVERS      64
#define RT_MAX_COMPLETIONS  256

typedef struct {
    spl_driver*     driver;
    spl_completion  completions[RT_MAX_COMPLETIONS];
    int64_t         completion_count;
} rt_driver_slot;

static rt_driver_slot g_slots[RT_MAX_DRIVERS];

/* ===== Platform Dispatch ===== */

spl_driver* spl_driver_create(int64_t queue_depth) {
#if defined(__linux__)
    /* epoll is the proven backend; io_uring path added in M4 */
    return spl_driver_create_epoll(queue_depth);
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
    if (d && d->vtable && d->vtable->destroy) {
        d->vtable->destroy(d);
    }
}

/* ===== C Vtable Dispatch Wrappers ===== */

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

int64_t spl_driver_poll(spl_driver* d, spl_completion* out,
                         int64_t max, int64_t timeout_ms) {
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

/* ===== Simple FFI — Flat Handle-Based API ===== */

static rt_driver_slot* slot_get(int64_t handle) {
    if (handle < 0 || handle >= RT_MAX_DRIVERS) return NULL;
    if (!g_slots[handle].driver) return NULL;
    return &g_slots[handle];
}

int64_t rt_driver_create(int64_t queue_depth) {
    for (int64_t i = 0; i < RT_MAX_DRIVERS; i++) {
        if (!g_slots[i].driver) {
            g_slots[i].driver = spl_driver_create(queue_depth);
            if (!g_slots[i].driver) return -1;
            g_slots[i].completion_count = 0;
            return i;
        }
    }
    return -1;
}

void rt_driver_destroy(int64_t handle) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return;
    spl_driver_destroy(s->driver);
    s->driver = NULL;
    s->completion_count = 0;
}

int64_t rt_driver_submit_accept(int64_t handle, int64_t listen_fd) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_accept(s->driver, listen_fd);
}

int64_t rt_driver_submit_connect(int64_t handle, int64_t fd,
                                  const char* addr, int64_t port) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_connect(s->driver, fd, addr, port);
}

int64_t rt_driver_submit_recv(int64_t handle, int64_t fd, int64_t buf_size) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_recv(s->driver, fd, buf_size);
}

int64_t rt_driver_submit_send(int64_t handle, int64_t fd,
                               const char* data, int64_t len) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_send(s->driver, fd, data, len);
}

int64_t rt_driver_submit_sendfile(int64_t handle, int64_t sock_fd,
                                   int64_t file_fd, int64_t offset,
                                   int64_t len) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_sendfile(s->driver, sock_fd, file_fd,
                                               offset, len);
}

int64_t rt_driver_submit_read(int64_t handle, int64_t fd,
                               int64_t buf_size, int64_t offset) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_read(s->driver, fd, buf_size, offset);
}

int64_t rt_driver_submit_write(int64_t handle, int64_t fd,
                                const char* data, int64_t len,
                                int64_t offset) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_write(s->driver, fd, data, len, offset);
}

int64_t rt_driver_submit_open(int64_t handle, const char* path,
                               int64_t flags, int64_t mode) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_open(s->driver, path, flags, mode);
}

int64_t rt_driver_submit_close(int64_t handle, int64_t fd) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_close(s->driver, fd);
}

int64_t rt_driver_submit_fsync(int64_t handle, int64_t fd) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_fsync(s->driver, fd);
}

int64_t rt_driver_submit_timeout(int64_t handle, int64_t timeout_ms) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_timeout(s->driver, timeout_ms);
}

int64_t rt_driver_flush(int64_t handle) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->flush(s->driver);
}

int64_t rt_driver_poll(int64_t handle, int64_t max, int64_t timeout_ms) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    if (max > RT_MAX_COMPLETIONS) max = RT_MAX_COMPLETIONS;
    int64_t n = s->driver->vtable->poll(s->driver, s->completions,
                                         max, timeout_ms);
    s->completion_count = n > 0 ? n : 0;
    return s->completion_count;
}

int64_t rt_driver_poll_id(int64_t handle, int64_t index) {
    rt_driver_slot* s = slot_get(handle);
    if (!s || index < 0 || index >= s->completion_count) return 0;
    return s->completions[index].id;
}

int64_t rt_driver_poll_result(int64_t handle, int64_t index) {
    rt_driver_slot* s = slot_get(handle);
    if (!s || index < 0 || index >= s->completion_count) return 0;
    return s->completions[index].result;
}

int64_t rt_driver_poll_flags(int64_t handle, int64_t index) {
    rt_driver_slot* s = slot_get(handle);
    if (!s || index < 0 || index >= s->completion_count) return 0;
    return s->completions[index].flags;
}

const char* rt_driver_poll_data(int64_t handle, int64_t index) {
    rt_driver_slot* s = slot_get(handle);
    if (!s || index < 0 || index >= s->completion_count) return "";
    if (!s->completions[index].data) return "";
    return s->completions[index].data;
}

int64_t rt_driver_poll_data_len(int64_t handle, int64_t index) {
    rt_driver_slot* s = slot_get(handle);
    if (!s || index < 0 || index >= s->completion_count) return 0;
    return s->completions[index].data_len;
}

bool rt_driver_cancel(int64_t handle, int64_t op_id) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return false;
    return s->driver->vtable->cancel(s->driver, op_id);
}

const char* rt_driver_backend_name(int64_t handle) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return "none";
    return s->driver->vtable->backend_name(s->driver);
}

bool rt_driver_supports_sendfile(int64_t handle) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return false;
    return s->driver->vtable->supports_sendfile(s->driver);
}

bool rt_driver_supports_zero_copy(int64_t handle) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return false;
    return s->driver->vtable->supports_zero_copy(s->driver);
}
