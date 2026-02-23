/*
 * Unified Async I/O Completion Driver — Interface Header
 *
 * Abstracts io_uring (Linux 5.1+), epoll (Linux <5.1), kqueue (macOS/FreeBSD),
 * and IOCP (Windows) behind a single completion-based (proactor) API.
 *
 * All backends implement this interface. The dispatch layer (async_driver.c)
 * selects the best available backend at creation time.
 *
 * Design:
 *   - All operations are submit-then-flush-then-poll (batched)
 *   - submit_* returns an op_id (monotonically increasing i64)
 *   - flush() pushes queued operations to the kernel
 *   - poll() harvests completions into caller-provided array
 *   - Readiness-based backends (epoll/kqueue) emulate completion internally
 *
 * Thread safety:
 *   - Each spl_driver instance is single-threaded (one per worker)
 *   - Thread-per-core model: no locking needed within a driver
 */

#ifndef SPL_ASYNC_DRIVER_H
#define SPL_ASYNC_DRIVER_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <stdbool.h>

/* ===== Opaque Driver Handle ===== */

typedef struct spl_driver spl_driver;

/* ===== Completion Result ===== */

typedef struct spl_completion {
    int64_t id;        /* operation ID from submit_* */
    int64_t result;    /* bytes transferred (>=0) or negative errno on error */
    int64_t flags;     /* platform-specific flags (e.g. IORING_CQE_F_MORE) */
} spl_completion;

/* ===== Backend Type ===== */

typedef enum {
    SPL_BACKEND_NONE     = 0,
    SPL_BACKEND_IO_URING = 1,
    SPL_BACKEND_EPOLL    = 2,
    SPL_BACKEND_KQUEUE   = 3,
    SPL_BACKEND_IOCP     = 4
} spl_backend_type;

/* ===== Lifecycle ===== */

/*
 * Create a new driver instance with the best available backend.
 * queue_depth: hint for internal queue size (e.g. 256, 1024, 4096)
 * Returns NULL on failure.
 */
spl_driver* spl_driver_create(int64_t queue_depth);

/*
 * Destroy driver and release all resources.
 * Cancels any pending operations.
 */
void spl_driver_destroy(spl_driver* d);

/* ===== Submit Operations ===== */
/* All return a unique op_id (>0) on success, or negative errno on error. */
/* Operations are queued until flush() is called.                          */

/* Network */
int64_t spl_driver_submit_accept(spl_driver* d, int64_t listen_fd);
int64_t spl_driver_submit_connect(spl_driver* d, int64_t fd, const char* addr, int64_t port);
int64_t spl_driver_submit_recv(spl_driver* d, int64_t fd, int64_t buf_size);
int64_t spl_driver_submit_send(spl_driver* d, int64_t fd, const char* data, int64_t len);
int64_t spl_driver_submit_sendfile(spl_driver* d, int64_t sock_fd, int64_t file_fd,
                                    int64_t offset, int64_t len);

/* File I/O */
int64_t spl_driver_submit_read(spl_driver* d, int64_t fd, int64_t buf_size, int64_t offset);
int64_t spl_driver_submit_write(spl_driver* d, int64_t fd, const char* data,
                                 int64_t len, int64_t offset);
int64_t spl_driver_submit_open(spl_driver* d, const char* path, int64_t flags, int64_t mode);
int64_t spl_driver_submit_close(spl_driver* d, int64_t fd);
int64_t spl_driver_submit_fsync(spl_driver* d, int64_t fd);

/* Timer */
int64_t spl_driver_submit_timeout(spl_driver* d, int64_t timeout_ms);

/* ===== Batch Control ===== */

/*
 * Flush all queued operations to the kernel.
 * Returns number of operations submitted, or negative errno on error.
 */
int64_t spl_driver_flush(spl_driver* d);

/* ===== Poll for Completions ===== */

/*
 * Wait for completions and fill the output array.
 * out:        caller-allocated array of spl_completion
 * max:        maximum completions to return
 * timeout_ms: -1 = block forever, 0 = non-blocking, >0 = timeout in ms
 * Returns number of completions, or negative errno on error.
 */
int64_t spl_driver_poll(spl_driver* d, spl_completion* out, int64_t max,
                         int64_t timeout_ms);

/* ===== Cancel ===== */

/*
 * Cancel a pending operation by op_id.
 * Returns true if cancellation was submitted, false if op not found.
 */
bool spl_driver_cancel(spl_driver* d, int64_t op_id);

/* ===== Query ===== */

const char* spl_driver_backend_name(spl_driver* d);
spl_backend_type spl_driver_backend_type(spl_driver* d);
bool spl_driver_supports_sendfile(spl_driver* d);
bool spl_driver_supports_zero_copy(spl_driver* d);

/* ===== Backend-Specific Constructors (internal) ===== */
/* Called by spl_driver_create() dispatch logic.         */

#if defined(__linux__)
spl_driver* spl_driver_create_uring(int64_t queue_depth);
spl_driver* spl_driver_create_epoll(int64_t queue_depth);
#elif defined(__APPLE__)
spl_driver* spl_driver_create_kqueue(int64_t queue_depth);
#elif defined(__FreeBSD__)
spl_driver* spl_driver_create_kqueue(int64_t queue_depth);
#elif defined(_WIN32)
spl_driver* spl_driver_create_iocp(int64_t queue_depth);
#endif

/* ===== Virtual Dispatch Table ===== */
/* Each backend fills this vtable at creation time. */

typedef struct spl_driver_vtable {
    void    (*destroy)(spl_driver* d);
    int64_t (*submit_accept)(spl_driver* d, int64_t listen_fd);
    int64_t (*submit_connect)(spl_driver* d, int64_t fd, const char* addr, int64_t port);
    int64_t (*submit_recv)(spl_driver* d, int64_t fd, int64_t buf_size);
    int64_t (*submit_send)(spl_driver* d, int64_t fd, const char* data, int64_t len);
    int64_t (*submit_sendfile)(spl_driver* d, int64_t sock_fd, int64_t file_fd,
                                int64_t offset, int64_t len);
    int64_t (*submit_read)(spl_driver* d, int64_t fd, int64_t buf_size, int64_t offset);
    int64_t (*submit_write)(spl_driver* d, int64_t fd, const char* data,
                             int64_t len, int64_t offset);
    int64_t (*submit_open)(spl_driver* d, const char* path, int64_t flags, int64_t mode);
    int64_t (*submit_close)(spl_driver* d, int64_t fd);
    int64_t (*submit_fsync)(spl_driver* d, int64_t fd);
    int64_t (*submit_timeout)(spl_driver* d, int64_t timeout_ms);
    int64_t (*flush)(spl_driver* d);
    int64_t (*poll)(spl_driver* d, spl_completion* out, int64_t max, int64_t timeout_ms);
    bool    (*cancel)(spl_driver* d, int64_t op_id);
    const char* (*backend_name)(spl_driver* d);
    spl_backend_type (*backend_type_fn)(spl_driver* d);
    bool    (*supports_sendfile)(spl_driver* d);
    bool    (*supports_zero_copy)(spl_driver* d);
} spl_driver_vtable;

/* ===== Base Driver Structure ===== */
/* Backends embed this as the first member for polymorphism. */

struct spl_driver {
    const spl_driver_vtable* vtable;
    int64_t next_op_id;   /* monotonically increasing operation ID counter */
};

/* ===== Legacy epoll FFI (used by event_loop.spl) ===== */

int64_t  rt_epoll_create(void);
int64_t  rt_epoll_ctl(int64_t epfd, int64_t op, int64_t fd, int64_t events);
/* Returns SplArray* of i64 pairs: [fd, events, fd, events, ...] */
struct SplArray;
struct SplArray* rt_epoll_wait(int64_t epfd, int64_t max_events, int64_t timeout_ms);
bool     rt_socket_set_nonblocking(int64_t fd, bool enabled);

#ifdef __cplusplus
}
#endif

#endif /* SPL_ASYNC_DRIVER_H */
