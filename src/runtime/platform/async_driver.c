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

/* Text results in the native Simple ABI are managed RuntimeValue strings,
 * not borrowed C-string pointers.  The Rust interpreter facade has a
 * separate raw pointer helper for its transient completion snapshot. */
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);

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
#if defined(SIMPLE_ASYNC_DRIVER_NO_EPOLL)
    /* The Rust facade calls the explicit constructor directly in this seed
     * build; keep the generic C entry honest for native C consumers. */
    const char* requested = getenv("SIMPLE_SOSIX_PROVIDER");
    if (!requested || !*requested || strcmp(requested, "auto") == 0) {
        return spl_driver_create_uring(queue_depth);
    }
    if (strcmp(requested, "io_uring") == 0 ||
        strcmp(requested, "io-uring") == 0 || strcmp(requested, "uring") == 0) {
        return spl_driver_create_uring(queue_depth);
    }
    return NULL;
#else
    const char* requested = getenv("SIMPLE_SOSIX_PROVIDER");
    if (requested && *requested &&
        (strcmp(requested, "io_uring") == 0 ||
         strcmp(requested, "io-uring") == 0 || strcmp(requested, "uring") == 0)) {
        /* Explicit requests fail closed if kernel policy or build support
         * prevents queue creation; never hide this behind epoll. */
        return spl_driver_create_uring(queue_depth);
    }
    if (requested && *requested && strcmp(requested, "auto") != 0 &&
        strcmp(requested, "epoll") != 0 && strcmp(requested, "reference") != 0 &&
        strcmp(requested, "rust-syscall") != 0) {
        return NULL;
    }
    if (!requested || !*requested || strcmp(requested, "auto") == 0) {
        spl_driver* uring = spl_driver_create_uring(queue_depth);
        if (uring) return uring;
    }
    return spl_driver_create_epoll(queue_depth);
#endif
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

/* The Rust runtime owns the hosted rt_driver_* facade on the interpreter
 * path.  Native C consumers can retain this adapter, but the seed build
 * defines this guard so the two owners cannot export the same ABI symbols. */
#ifndef SIMPLE_ASYNC_DRIVER_NO_FLAT_API

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
    for (int64_t i = 0; i < s->completion_count; i++)
        spl_completion_release(&s->completions[i]);
    spl_driver_destroy(s->driver);
    s->driver = NULL;
    s->completion_count = 0;
}

int64_t rt_driver_submit_accept(int64_t handle, int64_t listen_fd) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    return s->driver->vtable->submit_accept(s->driver, listen_fd);
}

/* Simple text arguments are passed as pointer+length at this ABI boundary;
 * they are not required to carry a trailing NUL.  The platform vtable still
 * uses C strings, so copy and validate the bounded input before dispatch. */
static char* copy_foreign_cstr(const char* value, int64_t length) {
    if (!value || length <= 0 || (uint64_t)length > SIZE_MAX - 1)
        return NULL;
    char* copy = (char*)malloc((size_t)length + 1);
    if (!copy) return NULL;
    memcpy(copy, value, (size_t)length);
    if (memchr(copy, '\0', (size_t)length) != NULL) {
        free(copy);
        return NULL;
    }
    copy[length] = '\0';
    return copy;
}

int64_t rt_driver_submit_connect(int64_t handle, int64_t fd,
                                  const char* addr, int64_t addr_len, int64_t port) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    char* address = copy_foreign_cstr(addr, addr_len);
    if (!address) return -EINVAL;
    int64_t result = s->driver->vtable->submit_connect(s->driver, fd, address, port);
    free(address);
    return result;
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
                               int64_t path_len, int64_t flags, int64_t mode) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return -EINVAL;
    char* path_copy = copy_foreign_cstr(path, path_len);
    if (!path_copy) return -EINVAL;
    int64_t result = s->driver->vtable->submit_open(s->driver, path_copy, flags, mode);
    free(path_copy);
    return result;
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
    /* A caller may intentionally ignore a payload. Retire the previous
     * snapshot before reusing its fixed storage so every owned buffer has a
     * deterministic release path. */
    for (int64_t i = 0; i < s->completion_count; i++)
        spl_completion_release(&s->completions[i]);
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

int64_t rt_driver_poll_data(int64_t handle, int64_t index) {
    rt_driver_slot* s = slot_get(handle);
    if (!s || index < 0 || index >= s->completion_count) return rt_string_new(NULL, 0);
    spl_completion* completion = &s->completions[index];
    int64_t value = rt_string_new((const uint8_t*)completion->data,
                                  completion->data_len > 0 ? (uint64_t)completion->data_len : 0);
    spl_completion_release(completion);
    return value;
}

int64_t rt_driver_poll_data_len(int64_t handle, int64_t index) {
    rt_driver_slot* s = slot_get(handle);
    if (!s || index < 0 || index >= s->completion_count) return 0;
    return s->completions[index].data_len;
}

/* Borrowed views for the interpreter's raw completion ABI.  The completion
 * remains owned by the slot until the next poll or driver destruction; the
 * managed rt_driver_poll_data() above is the ownership-transferring API. */
const uint8_t* rt_driver_poll_data_ptr(int64_t handle, int64_t index) {
    rt_driver_slot* s = slot_get(handle);
    if (!s || index < 0 || index >= s->completion_count) return NULL;
    spl_completion* completion = &s->completions[index];
    return completion->data_len > 0 ? (const uint8_t*)completion->data : NULL;
}

bool rt_driver_cancel(int64_t handle, int64_t op_id) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return false;
    return s->driver->vtable->cancel(s->driver, op_id);
}

int64_t rt_driver_backend_name(int64_t handle) {
    rt_driver_slot* s = slot_get(handle);
    if (!s) return rt_string_new((const uint8_t*)"none", 4);
    const char* name = s->driver->vtable->backend_name(s->driver);
    return rt_string_new((const uint8_t*)name, (uint64_t)strlen(name));
}

/* Borrowed static backend name for the interpreter's raw completion ABI. */
const char* rt_driver_backend_name_ptr(int64_t handle) {
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

#endif /* SIMPLE_ASYNC_DRIVER_NO_FLAT_API */

void spl_completion_release(spl_completion* completion) {
    if (!completion) return;
    free(completion->data);
    completion->data = NULL;
    completion->data_len = 0;
}
