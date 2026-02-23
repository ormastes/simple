/*
 * Linux io_uring Backend for spl_driver
 *
 * Implements the unified async I/O completion driver interface using
 * io_uring (Linux 5.1+). Falls back to NULL when io_uring is not
 * available at compile time (SPL_HAS_IO_URING not defined) or at
 * runtime (kernel too old / init failure).
 *
 * Design notes:
 *   - Single-threaded, no locking (thread-per-core model)
 *   - Buffer tracking via open-addressed hash table keyed on op_id
 *   - sendfile(2) is not natively supported by io_uring pre-6.x;
 *     we submit a NOP and execute sendfile(2) in poll() on completion
 *   - All submit_* calls queue into the SQ; flush() pushes to kernel
 */

#if defined(__linux__)

#ifdef SPL_HAS_IO_URING

#define _GNU_SOURCE
#include "async_driver.h"
#include <liburing.h>

#include <sys/sendfile.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <linux/time_types.h>  /* __kernel_timespec */

/* ===================================================================
 * Buffer tracking — open-addressed hash table {op_id -> buf_entry}
 * =================================================================== */

enum {
    BUF_OP_RECV    = 1,
    BUF_OP_READ    = 2,
    BUF_OP_CONNECT = 3,
    BUF_OP_OPEN    = 4,
    BUF_OP_TIMEOUT = 5
};

typedef struct buf_entry {
    int64_t op_id;      /* 0 = empty slot */
    char*   buf;        /* allocated buffer (recv/read) or sockaddr (connect) */
    int64_t len;        /* buffer length */
    int     op_type;    /* BUF_OP_* */
    char*   path;       /* strdup'd path for open ops, NULL otherwise */
} buf_entry;

/* Deferred sendfile operation: queued on submit, executed in poll */
typedef struct sendfile_op {
    int64_t op_id;
    int64_t sock_fd;
    int64_t file_fd;
    int64_t offset;
    int64_t len;
} sendfile_op;

typedef struct {
    spl_driver       base;
    struct io_uring  ring;
    buf_entry*       bufs;
    int64_t          bufs_cap;
    int64_t          bufs_count;
    int64_t          pending_submits;
    sendfile_op*     sf_ops;
    int64_t          sf_count;
    int64_t          sf_cap;
} uring_driver;

/* ---- hash helpers ---- */

static inline int64_t hash_slot(int64_t op_id, int64_t cap)
{
    /* Fibonacci hashing for good distribution */
    uint64_t h = (uint64_t)op_id * UINT64_C(11400714819323198485);
    return (int64_t)(h >> (64 - 20)) & (cap - 1);  /* cap is power of 2 */
}

static void bufs_grow(uring_driver* ud)
{
    int64_t old_cap = ud->bufs_cap;
    buf_entry* old  = ud->bufs;

    int64_t new_cap = old_cap ? old_cap * 2 : 64;
    buf_entry* tbl  = (buf_entry*)calloc((size_t)new_cap, sizeof(buf_entry));
    if (!tbl) return;

    /* rehash */
    for (int64_t i = 0; i < old_cap; i++) {
        if (old[i].op_id == 0) continue;
        int64_t slot = hash_slot(old[i].op_id, new_cap);
        while (tbl[slot].op_id != 0)
            slot = (slot + 1) & (new_cap - 1);
        tbl[slot] = old[i];
    }

    ud->bufs     = tbl;
    ud->bufs_cap = new_cap;
    free(old);
}

static void bufs_put(uring_driver* ud, int64_t op_id, char* buf,
                     int64_t len, int op_type, char* path)
{
    /* grow if load factor > 0.6 */
    if (ud->bufs_count * 10 >= ud->bufs_cap * 6)
        bufs_grow(ud);

    int64_t slot = hash_slot(op_id, ud->bufs_cap);
    while (ud->bufs[slot].op_id != 0)
        slot = (slot + 1) & (ud->bufs_cap - 1);

    ud->bufs[slot].op_id   = op_id;
    ud->bufs[slot].buf     = buf;
    ud->bufs[slot].len     = len;
    ud->bufs[slot].op_type = op_type;
    ud->bufs[slot].path    = path;
    ud->bufs_count++;
}

/* Find and remove entry. Returns the entry (with op_id=0 if not found). */
static buf_entry bufs_take(uring_driver* ud, int64_t op_id)
{
    buf_entry empty = {0};
    if (ud->bufs_cap == 0) return empty;

    int64_t slot = hash_slot(op_id, ud->bufs_cap);
    int64_t start = slot;

    for (;;) {
        if (ud->bufs[slot].op_id == op_id) {
            buf_entry e = ud->bufs[slot];
            ud->bufs[slot].op_id = 0;
            ud->bufs[slot].buf   = NULL;
            ud->bufs[slot].path  = NULL;
            ud->bufs_count--;

            /* re-probe subsequent entries to fix the chain */
            int64_t next = (slot + 1) & (ud->bufs_cap - 1);
            while (ud->bufs[next].op_id != 0) {
                buf_entry tmp = ud->bufs[next];
                ud->bufs[next].op_id = 0;
                ud->bufs[next].buf   = NULL;
                ud->bufs[next].path  = NULL;
                ud->bufs_count--;
                bufs_put(ud, tmp.op_id, tmp.buf, tmp.len, tmp.op_type, tmp.path);
                next = (next + 1) & (ud->bufs_cap - 1);
            }
            return e;
        }
        if (ud->bufs[slot].op_id == 0)
            return empty;
        slot = (slot + 1) & (ud->bufs_cap - 1);
        if (slot == start)
            return empty;
    }
}

/* ---- sendfile op helpers ---- */

static void sf_push(uring_driver* ud, int64_t op_id, int64_t sock_fd,
                    int64_t file_fd, int64_t offset, int64_t len)
{
    if (ud->sf_count >= ud->sf_cap) {
        int64_t new_cap = ud->sf_cap ? ud->sf_cap * 2 : 16;
        sendfile_op* new_arr = (sendfile_op*)realloc(
            ud->sf_ops, (size_t)new_cap * sizeof(sendfile_op));
        if (!new_arr) return;
        ud->sf_ops = new_arr;
        ud->sf_cap = new_cap;
    }
    ud->sf_ops[ud->sf_count++] = (sendfile_op){
        .op_id   = op_id,
        .sock_fd = sock_fd,
        .file_fd = file_fd,
        .offset  = offset,
        .len     = len
    };
}

/* Find sendfile op by op_id, remove it, return a copy.  Returns op with op_id=0 if not found. */
static sendfile_op sf_take(uring_driver* ud, int64_t op_id)
{
    for (int64_t i = 0; i < ud->sf_count; i++) {
        if (ud->sf_ops[i].op_id == op_id) {
            sendfile_op found = ud->sf_ops[i];
            /* swap with last and shrink */
            ud->sf_ops[i] = ud->sf_ops[ud->sf_count - 1];
            ud->sf_count--;
            return found;
        }
    }
    return (sendfile_op){0};
}

/* ===================================================================
 * Helper: allocate next op_id
 * =================================================================== */

static inline int64_t next_id(spl_driver* d)
{
    return ++d->next_op_id;
}

/* Cast base pointer to uring_driver */
static inline uring_driver* UD(spl_driver* d)
{
    return (uring_driver*)d;
}

/* Get an SQE, returns NULL and sets errno if the ring is full */
static struct io_uring_sqe* get_sqe(uring_driver* ud)
{
    struct io_uring_sqe* sqe = io_uring_get_sqe(&ud->ring);
    if (!sqe) {
        /* SQ is full; flush first, then retry */
        io_uring_submit(&ud->ring);
        ud->pending_submits = 0;
        sqe = io_uring_get_sqe(&ud->ring);
    }
    return sqe;
}

/* ===================================================================
 * vtable implementations
 * =================================================================== */

/* ---- destroy ---- */

static void uring_destroy(spl_driver* d)
{
    uring_driver* ud = UD(d);

    /* Free all tracked buffers */
    if (ud->bufs) {
        for (int64_t i = 0; i < ud->bufs_cap; i++) {
            if (ud->bufs[i].op_id != 0) {
                free(ud->bufs[i].buf);
                free(ud->bufs[i].path);
            }
        }
        free(ud->bufs);
    }

    free(ud->sf_ops);
    io_uring_queue_exit(&ud->ring);
    free(ud);
}

/* ---- submit_accept ---- */

static int64_t uring_submit_accept(spl_driver* d, int64_t listen_fd)
{
    uring_driver* ud = UD(d);
    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) return -EAGAIN;

    int64_t id = next_id(d);
    io_uring_prep_accept(sqe, (int)listen_fd, NULL, NULL, 0);
    io_uring_sqe_set_data64(sqe, (uint64_t)id);
    ud->pending_submits++;
    return id;
}

/* ---- submit_connect ---- */

static int64_t uring_submit_connect(spl_driver* d, int64_t fd,
                                    const char* addr, int64_t port)
{
    uring_driver* ud = UD(d);
    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) return -EAGAIN;

    /* Allocate sockaddr_in and fill it */
    struct sockaddr_in* sa = (struct sockaddr_in*)calloc(1, sizeof(*sa));
    if (!sa) return -ENOMEM;

    sa->sin_family = AF_INET;
    sa->sin_port   = htons((uint16_t)port);
    if (inet_pton(AF_INET, addr, &sa->sin_addr) != 1) {
        free(sa);
        return -EINVAL;
    }

    int64_t id = next_id(d);
    io_uring_prep_connect(sqe, (int)fd, (struct sockaddr*)sa, sizeof(*sa));
    io_uring_sqe_set_data64(sqe, (uint64_t)id);

    /* Track the sockaddr so we can free it after completion */
    bufs_put(ud, id, (char*)sa, (int64_t)sizeof(*sa), BUF_OP_CONNECT, NULL);
    ud->pending_submits++;
    return id;
}

/* ---- submit_recv ---- */

static int64_t uring_submit_recv(spl_driver* d, int64_t fd, int64_t buf_size)
{
    uring_driver* ud = UD(d);

    char* buf = (char*)malloc((size_t)buf_size);
    if (!buf) return -ENOMEM;

    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) {
        free(buf);
        return -EAGAIN;
    }

    int64_t id = next_id(d);
    io_uring_prep_recv(sqe, (int)fd, buf, (unsigned)buf_size, 0);
    io_uring_sqe_set_data64(sqe, (uint64_t)id);

    bufs_put(ud, id, buf, buf_size, BUF_OP_RECV, NULL);
    ud->pending_submits++;
    return id;
}

/* ---- submit_send ---- */

static int64_t uring_submit_send(spl_driver* d, int64_t fd,
                                 const char* data, int64_t len)
{
    uring_driver* ud = UD(d);
    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) return -EAGAIN;

    int64_t id = next_id(d);
    io_uring_prep_send(sqe, (int)fd, data, (unsigned)len, 0);
    io_uring_sqe_set_data64(sqe, (uint64_t)id);

    /* Caller owns data lifetime; nothing to track */
    ud->pending_submits++;
    return id;
}

/* ---- submit_sendfile ---- */

static int64_t uring_submit_sendfile(spl_driver* d, int64_t sock_fd,
                                     int64_t file_fd, int64_t offset,
                                     int64_t len)
{
    uring_driver* ud = UD(d);
    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) return -EAGAIN;

    int64_t id = next_id(d);

    /*
     * io_uring gained native splice/sendfile support in Linux 5.6+,
     * but the API is complex (requires splice + pipe).  Instead we
     * submit a NOP here and execute sendfile(2) synchronously when
     * this NOP completes in poll().  For high-throughput cases this
     * is still effective because sendfile(2) uses zero-copy DMA on
     * supported filesystems.
     */
    io_uring_prep_nop(sqe);
    io_uring_sqe_set_data64(sqe, (uint64_t)id);

    sf_push(ud, id, sock_fd, file_fd, offset, len);
    ud->pending_submits++;
    return id;
}

/* ---- submit_read ---- */

static int64_t uring_submit_read(spl_driver* d, int64_t fd,
                                 int64_t buf_size, int64_t offset)
{
    uring_driver* ud = UD(d);

    char* buf = (char*)malloc((size_t)buf_size);
    if (!buf) return -ENOMEM;

    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) {
        free(buf);
        return -EAGAIN;
    }

    int64_t id = next_id(d);
    io_uring_prep_read(sqe, (int)fd, buf, (unsigned)buf_size, (uint64_t)offset);
    io_uring_sqe_set_data64(sqe, (uint64_t)id);

    bufs_put(ud, id, buf, buf_size, BUF_OP_READ, NULL);
    ud->pending_submits++;
    return id;
}

/* ---- submit_write ---- */

static int64_t uring_submit_write(spl_driver* d, int64_t fd,
                                  const char* data, int64_t len,
                                  int64_t offset)
{
    uring_driver* ud = UD(d);
    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) return -EAGAIN;

    int64_t id = next_id(d);
    io_uring_prep_write(sqe, (int)fd, data, (unsigned)len, (uint64_t)offset);
    io_uring_sqe_set_data64(sqe, (uint64_t)id);

    /* Caller owns data lifetime */
    ud->pending_submits++;
    return id;
}

/* ---- submit_open ---- */

static int64_t uring_submit_open(spl_driver* d, const char* path,
                                 int64_t flags, int64_t mode)
{
    uring_driver* ud = UD(d);

    char* path_copy = strdup(path);
    if (!path_copy) return -ENOMEM;

    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) {
        free(path_copy);
        return -EAGAIN;
    }

    int64_t id = next_id(d);
    io_uring_prep_openat(sqe, AT_FDCWD, path_copy, (int)flags, (mode_t)mode);
    io_uring_sqe_set_data64(sqe, (uint64_t)id);

    bufs_put(ud, id, NULL, 0, BUF_OP_OPEN, path_copy);
    ud->pending_submits++;
    return id;
}

/* ---- submit_close ---- */

static int64_t uring_submit_close(spl_driver* d, int64_t fd)
{
    uring_driver* ud = UD(d);
    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) return -EAGAIN;

    int64_t id = next_id(d);
    io_uring_prep_close(sqe, (int)fd);
    io_uring_sqe_set_data64(sqe, (uint64_t)id);

    ud->pending_submits++;
    return id;
}

/* ---- submit_fsync ---- */

static int64_t uring_submit_fsync(spl_driver* d, int64_t fd)
{
    uring_driver* ud = UD(d);
    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) return -EAGAIN;

    int64_t id = next_id(d);
    io_uring_prep_fsync(sqe, (int)fd, 0);
    io_uring_sqe_set_data64(sqe, (uint64_t)id);

    ud->pending_submits++;
    return id;
}

/* ---- submit_timeout ---- */

static int64_t uring_submit_timeout(spl_driver* d, int64_t timeout_ms)
{
    uring_driver* ud = UD(d);

    struct __kernel_timespec* ts =
        (struct __kernel_timespec*)calloc(1, sizeof(*ts));
    if (!ts) return -ENOMEM;

    ts->tv_sec  = timeout_ms / 1000;
    ts->tv_nsec = (timeout_ms % 1000) * 1000000LL;

    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) {
        free(ts);
        return -EAGAIN;
    }

    int64_t id = next_id(d);
    io_uring_prep_timeout(sqe, ts, 0, 0);
    io_uring_sqe_set_data64(sqe, (uint64_t)id);

    bufs_put(ud, id, (char*)ts, (int64_t)sizeof(*ts), BUF_OP_TIMEOUT, NULL);
    ud->pending_submits++;
    return id;
}

/* ---- flush ---- */

static int64_t uring_flush(spl_driver* d)
{
    uring_driver* ud = UD(d);
    int ret = io_uring_submit(&ud->ring);
    if (ret < 0)
        return (int64_t)ret;

    int64_t submitted = ud->pending_submits;
    ud->pending_submits = 0;
    return submitted;
}

/* ---- poll ---- */

static int64_t uring_poll(spl_driver* d, spl_completion* out, int64_t max,
                          int64_t timeout_ms)
{
    uring_driver* ud = UD(d);
    if (max <= 0) return 0;

    struct io_uring_cqe* cqe = NULL;
    int64_t count = 0;
    int ret;

    /* Wait for the first completion with the requested timeout */
    if (timeout_ms < 0) {
        /* Block indefinitely */
        ret = io_uring_wait_cqe(&ud->ring, &cqe);
    } else if (timeout_ms == 0) {
        /* Non-blocking peek */
        ret = io_uring_peek_cqe(&ud->ring, &cqe);
    } else {
        /* Timed wait */
        struct __kernel_timespec ts;
        ts.tv_sec  = timeout_ms / 1000;
        ts.tv_nsec = (timeout_ms % 1000) * 1000000LL;
        ret = io_uring_wait_cqe_timeout(&ud->ring, &cqe, &ts);
    }

    if (ret < 0) {
        /* -ETIME or -EAGAIN are not fatal: just means no completions */
        if (ret == -ETIME || ret == -EAGAIN)
            return 0;
        return (int64_t)ret;
    }

    /* Process the first CQE we already have, then peek for more */
    while (cqe && count < max) {
        int64_t op_id  = (int64_t)io_uring_cqe_get_data64(cqe);
        int64_t result = (int64_t)cqe->res;
        int64_t flags  = (int64_t)cqe->flags;

        /* Check if this is a sendfile NOP */
        sendfile_op sf = sf_take(ud, op_id);
        if (sf.op_id != 0) {
            /* Execute the actual sendfile(2) syscall now */
            off_t sf_offset = (off_t)sf.offset;
            ssize_t sent = sendfile((int)sf.sock_fd, (int)sf.file_fd,
                                    &sf_offset, (size_t)sf.len);
            result = (sent >= 0) ? (int64_t)sent : (int64_t)(-errno);
            flags  = 0;
        }

        /* Free any tracked buffer for this op */
        buf_entry be = bufs_take(ud, op_id);
        if (be.op_id != 0) {
            free(be.buf);
            free(be.path);
        }

        out[count].id     = op_id;
        out[count].result = result;
        out[count].flags  = flags;
        count++;

        io_uring_cqe_seen(&ud->ring, cqe);

        /* Try to peek the next CQE */
        if (count < max) {
            ret = io_uring_peek_cqe(&ud->ring, &cqe);
            if (ret < 0)
                break;  /* no more completions ready */
        } else {
            break;
        }
    }

    return count;
}

/* ---- cancel ---- */

static bool uring_cancel(spl_driver* d, int64_t op_id)
{
    uring_driver* ud = UD(d);
    struct io_uring_sqe* sqe = get_sqe(ud);
    if (!sqe) return false;

    io_uring_prep_cancel64(sqe, (uint64_t)op_id, 0);
    io_uring_sqe_set_data64(sqe, 0);  /* cancel completions use id=0 */

    int ret = io_uring_submit(&ud->ring);
    return ret >= 0;
}

/* ---- query functions ---- */

static const char* uring_backend_name(spl_driver* d)
{
    (void)d;
    return "io_uring";
}

static spl_backend_type uring_backend_type_fn(spl_driver* d)
{
    (void)d;
    return SPL_BACKEND_IO_URING;
}

static bool uring_supports_sendfile(spl_driver* d)
{
    (void)d;
    return true;  /* supported via sendfile(2) syscall fallback */
}

static bool uring_supports_zero_copy(spl_driver* d)
{
    (void)d;
    /*
     * io_uring supports IORING_OP_SEND_ZC on Linux 6.0+.
     * We don't use it yet, so report false.
     */
    return false;
}

/* ===================================================================
 * vtable
 * =================================================================== */

static const spl_driver_vtable uring_vtable = {
    .destroy           = uring_destroy,
    .submit_accept     = uring_submit_accept,
    .submit_connect    = uring_submit_connect,
    .submit_recv       = uring_submit_recv,
    .submit_send       = uring_submit_send,
    .submit_sendfile   = uring_submit_sendfile,
    .submit_read       = uring_submit_read,
    .submit_write      = uring_submit_write,
    .submit_open       = uring_submit_open,
    .submit_close      = uring_submit_close,
    .submit_fsync      = uring_submit_fsync,
    .submit_timeout    = uring_submit_timeout,
    .flush             = uring_flush,
    .poll              = uring_poll,
    .cancel            = uring_cancel,
    .backend_name      = uring_backend_name,
    .backend_type_fn   = uring_backend_type_fn,
    .supports_sendfile = uring_supports_sendfile,
    .supports_zero_copy = uring_supports_zero_copy
};

/* ===================================================================
 * Constructor
 * =================================================================== */

spl_driver* spl_driver_create_uring(int64_t queue_depth)
{
    if (queue_depth <= 0)
        queue_depth = 256;

    /* Clamp to a reasonable range */
    if (queue_depth < 16)
        queue_depth = 16;
    if (queue_depth > 32768)
        queue_depth = 32768;

    /* Round up to next power of 2 (io_uring requires this) */
    int64_t p = 1;
    while (p < queue_depth)
        p <<= 1;
    queue_depth = p;

    uring_driver* ud = (uring_driver*)calloc(1, sizeof(uring_driver));
    if (!ud) return NULL;

    /*
     * Attempt to initialize the io_uring instance.
     * This will fail gracefully on kernels < 5.1 or when
     * the io_uring syscalls are blocked by seccomp.
     */
    int ret = io_uring_queue_init((unsigned)queue_depth, &ud->ring, 0);
    if (ret < 0) {
        free(ud);
        return NULL;  /* runtime detection: io_uring not available */
    }

    ud->base.vtable     = &uring_vtable;
    ud->base.next_op_id = 0;
    ud->bufs            = NULL;
    ud->bufs_cap        = 0;
    ud->bufs_count      = 0;
    ud->pending_submits = 0;
    ud->sf_ops          = NULL;
    ud->sf_count        = 0;
    ud->sf_cap          = 0;

    /* Pre-allocate the buffer hash table */
    bufs_grow(ud);

    return &ud->base;
}

#else /* !SPL_HAS_IO_URING */

/*
 * Stub: io_uring headers not available at compile time.
 * Returns NULL so the dispatch layer falls through to epoll.
 */
#include "async_driver.h"

spl_driver* spl_driver_create_uring(int64_t q)
{
    (void)q;
    return NULL;
}

#endif /* SPL_HAS_IO_URING */

#endif /* __linux__ */
