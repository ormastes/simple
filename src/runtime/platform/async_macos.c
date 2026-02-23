/*
 * Async I/O Driver — macOS kqueue Backend
 *
 * kqueue + threadpool implementation:
 *   - Network I/O: kqueue readiness notification, then perform syscall, yield completion
 *   - File I/O:    threadpool workers (kqueue has no native file async)
 *   - Timers:      EVFILT_TIMER (native kqueue timer support)
 *   - sendfile:    macOS sendfile(fd, s, offset, &len, NULL, 0)
 *
 * Pending operations are tracked in an open-addressing hash table keyed by op_id.
 * The threadpool uses a work_queue/done_queue pair protected by mutexes.
 */

#if defined(__APPLE__)

#include "async_driver.h"

#include <sys/event.h>
#include <sys/socket.h>
#include <sys/uio.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <sched.h>

/* ================================================================
 * Operation Types
 * ================================================================ */

#define OP_ACCEPT   1
#define OP_CONNECT  2
#define OP_RECV     3
#define OP_SEND     4
#define OP_SENDFILE 5
#define OP_READ     6
#define OP_WRITE    7
#define OP_OPEN     8
#define OP_CLOSE    9
#define OP_FSYNC    10
#define OP_TIMEOUT  11

/* ================================================================
 * Pending Operation
 * ================================================================ */

typedef struct {
    int64_t     op_id;
    int         op_type;
    int64_t     fd;
    char*       buf;
    int64_t     buf_len;
    int64_t     offset;
    const char* path;         /* for open: owned copy */
    int64_t     flags;        /* for open: O_* flags */
    int64_t     mode;         /* for open: mode_t */
    int64_t     sock_fd;      /* for sendfile */
    int64_t     file_fd;      /* for sendfile */
    int64_t     timeout_ms;   /* for timeout */
    const char* addr;         /* for connect: owned copy */
    int64_t     port;         /* for connect */
    int         submitted;    /* 1 if flushed to kqueue / threadpool */
    int         completed;    /* 1 if done */
    int64_t     result;       /* completion result */
} pending_op;

/* ================================================================
 * Driver Structure
 * ================================================================ */

typedef struct {
    spl_driver      base;
    int             kq_fd;

    /* open-addressing hash table for pending ops */
    pending_op*     ops;
    int64_t         ops_cap;
    int64_t         ops_count;

    /* threadpool for file I/O */
    pthread_t*      pool_threads;
    int             pool_size;

    /* work queue: ring buffer of pending_op pointers */
    pending_op**    work_queue;
    int64_t         work_head;
    int64_t         work_tail;
    int64_t         work_cap;
    pthread_mutex_t work_mutex;
    pthread_cond_t  work_cond;

    /* done queue: ring buffer of completions from workers */
    spl_completion* done_queue;
    int64_t         done_head;
    int64_t         done_tail;
    int64_t         done_cap;
    pthread_mutex_t done_mutex;

    volatile int    shutdown;
} kqueue_driver;

/* ================================================================
 * Hash Table Helpers
 * ================================================================ */

static int64_t hash_slot(int64_t op_id, int64_t cap) {
    return (uint64_t)op_id % (uint64_t)cap;
}

static pending_op* find_op(kqueue_driver* kd, int64_t op_id) {
    int64_t idx = hash_slot(op_id, kd->ops_cap);
    for (int64_t i = 0; i < kd->ops_cap; i++) {
        int64_t slot = (idx + i) % kd->ops_cap;
        if (kd->ops[slot].op_id == op_id)
            return &kd->ops[slot];
        if (kd->ops[slot].op_id == 0)
            return NULL;
    }
    return NULL;
}

static pending_op* insert_op(kqueue_driver* kd, int64_t op_id) {
    if (kd->ops_count * 2 >= kd->ops_cap) {
        /* rehash */
        int64_t new_cap = kd->ops_cap * 2;
        pending_op* new_ops = (pending_op*)calloc((size_t)new_cap, sizeof(pending_op));
        if (!new_ops) return NULL;
        for (int64_t i = 0; i < kd->ops_cap; i++) {
            if (kd->ops[i].op_id != 0) {
                int64_t s = hash_slot(kd->ops[i].op_id, new_cap);
                while (new_ops[s].op_id != 0)
                    s = (s + 1) % new_cap;
                new_ops[s] = kd->ops[i];
            }
        }
        free(kd->ops);
        kd->ops = new_ops;
        kd->ops_cap = new_cap;
    }
    int64_t idx = hash_slot(op_id, kd->ops_cap);
    while (kd->ops[idx].op_id != 0)
        idx = (idx + 1) % kd->ops_cap;
    kd->ops[idx].op_id = op_id;
    kd->ops_count++;
    return &kd->ops[idx];
}

static void remove_op(kqueue_driver* kd, int64_t op_id) {
    int64_t idx = hash_slot(op_id, kd->ops_cap);
    for (int64_t i = 0; i < kd->ops_cap; i++) {
        int64_t slot = (idx + i) % kd->ops_cap;
        if (kd->ops[slot].op_id == op_id) {
            if (kd->ops[slot].buf) free(kd->ops[slot].buf);
            if (kd->ops[slot].path) free((void*)kd->ops[slot].path);
            if (kd->ops[slot].addr) free((void*)kd->ops[slot].addr);
            memset(&kd->ops[slot], 0, sizeof(pending_op));
            kd->ops_count--;
            /* rehash subsequent cluster entries */
            int64_t next = (slot + 1) % kd->ops_cap;
            while (kd->ops[next].op_id != 0) {
                pending_op tmp = kd->ops[next];
                memset(&kd->ops[next], 0, sizeof(pending_op));
                kd->ops_count--;
                pending_op* re = insert_op(kd, tmp.op_id);
                if (re) {
                    int64_t saved_id = re->op_id;
                    *re = tmp;
                    re->op_id = saved_id;
                }
                next = (next + 1) % kd->ops_cap;
            }
            return;
        }
        if (kd->ops[slot].op_id == 0) return;
    }
}

/* ================================================================
 * Threadpool Worker
 * ================================================================ */

static void execute_file_op(pending_op* op) {
    switch (op->op_type) {
    case OP_READ: {
        op->buf = (char*)malloc((size_t)op->buf_len);
        if (!op->buf) { op->result = -ENOMEM; break; }
        ssize_t r = pread((int)op->fd, op->buf, (size_t)op->buf_len, (off_t)op->offset);
        op->result = (r >= 0) ? r : -errno;
        break;
    }
    case OP_WRITE: {
        ssize_t r = pwrite((int)op->fd, op->buf, (size_t)op->buf_len, (off_t)op->offset);
        op->result = (r >= 0) ? r : -errno;
        break;
    }
    case OP_OPEN: {
        int fd = open(op->path, (int)op->flags, (mode_t)op->mode);
        op->result = (fd >= 0) ? fd : -errno;
        break;
    }
    case OP_CLOSE:
        op->result = (close((int)op->fd) == 0) ? 0 : -errno;
        break;
    case OP_FSYNC:
        op->result = (fsync((int)op->fd) == 0) ? 0 : -errno;
        break;
    default:
        op->result = -ENOTSUP;
        break;
    }
    op->completed = 1;
}

static void* threadpool_worker(void* arg) {
    kqueue_driver* kd = (kqueue_driver*)arg;
    while (!kd->shutdown) {
        pending_op* op = NULL;

        pthread_mutex_lock(&kd->work_mutex);
        while (kd->work_head == kd->work_tail && !kd->shutdown)
            pthread_cond_wait(&kd->work_cond, &kd->work_mutex);
        if (kd->shutdown) {
            pthread_mutex_unlock(&kd->work_mutex);
            break;
        }
        op = kd->work_queue[kd->work_head % kd->work_cap];
        kd->work_head++;
        pthread_mutex_unlock(&kd->work_mutex);

        if (!op) continue;
        execute_file_op(op);

        /* push completion to done queue */
        pthread_mutex_lock(&kd->done_mutex);
        int64_t next_tail = (kd->done_tail + 1) % kd->done_cap;
        if (next_tail != kd->done_head % kd->done_cap) {
            kd->done_queue[kd->done_tail % kd->done_cap] = (spl_completion){
                .id = op->op_id, .result = op->result, .flags = 0
            };
            kd->done_tail++;
        }
        pthread_mutex_unlock(&kd->done_mutex);
    }
    return NULL;
}

/* ================================================================
 * Submit Helpers
 * ================================================================ */

static int64_t next_id(kqueue_driver* kd) {
    return ++kd->base.next_op_id;
}

static void set_nonblocking(int fd) {
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags >= 0) fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}

/* ================================================================
 * VTable Implementations
 * ================================================================ */

static void kq_destroy(spl_driver* d) {
    kqueue_driver* kd = (kqueue_driver*)d;

    /* signal threadpool shutdown */
    kd->shutdown = 1;
    pthread_mutex_lock(&kd->work_mutex);
    pthread_cond_broadcast(&kd->work_cond);
    pthread_mutex_unlock(&kd->work_mutex);
    for (int i = 0; i < kd->pool_size; i++)
        pthread_join(kd->pool_threads[i], NULL);
    free(kd->pool_threads);

    pthread_mutex_destroy(&kd->work_mutex);
    pthread_cond_destroy(&kd->work_cond);
    pthread_mutex_destroy(&kd->done_mutex);

    free(kd->work_queue);
    free(kd->done_queue);

    /* free pending ops */
    for (int64_t i = 0; i < kd->ops_cap; i++) {
        if (kd->ops[i].op_id != 0) {
            if (kd->ops[i].buf) free(kd->ops[i].buf);
            if (kd->ops[i].path) free((void*)kd->ops[i].path);
            if (kd->ops[i].addr) free((void*)kd->ops[i].addr);
        }
    }
    free(kd->ops);

    close(kd->kq_fd);
    free(kd);
}

static int64_t kq_submit_accept(spl_driver* d, int64_t listen_fd) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t id = next_id(kd);
    pending_op* op = insert_op(kd, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_ACCEPT;
    op->fd = listen_fd;
    return id;
}

static int64_t kq_submit_connect(spl_driver* d, int64_t fd,
                                  const char* addr, int64_t port) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t id = next_id(kd);
    pending_op* op = insert_op(kd, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_CONNECT;
    op->fd = fd;
    op->addr = strdup(addr);
    op->port = port;
    return id;
}

static int64_t kq_submit_recv(spl_driver* d, int64_t fd, int64_t buf_size) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t id = next_id(kd);
    pending_op* op = insert_op(kd, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_RECV;
    op->fd = fd;
    op->buf_len = buf_size;
    return id;
}

static int64_t kq_submit_send(spl_driver* d, int64_t fd,
                               const char* data, int64_t len) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t id = next_id(kd);
    pending_op* op = insert_op(kd, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_SEND;
    op->fd = fd;
    op->buf = (char*)malloc((size_t)len);
    if (!op->buf) { remove_op(kd, id); return -ENOMEM; }
    memcpy(op->buf, data, (size_t)len);
    op->buf_len = len;
    return id;
}

static int64_t kq_submit_sendfile(spl_driver* d, int64_t sock_fd,
                                   int64_t file_fd, int64_t offset,
                                   int64_t len) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t id = next_id(kd);
    pending_op* op = insert_op(kd, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_SENDFILE;
    op->sock_fd = sock_fd;
    op->file_fd = file_fd;
    op->offset = offset;
    op->buf_len = len;
    return id;
}

static int64_t kq_submit_read(spl_driver* d, int64_t fd,
                               int64_t buf_size, int64_t offset) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t id = next_id(kd);
    pending_op* op = insert_op(kd, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_READ;
    op->fd = fd;
    op->buf_len = buf_size;
    op->offset = offset;
    return id;
}

static int64_t kq_submit_write(spl_driver* d, int64_t fd,
                                const char* data, int64_t len,
                                int64_t offset) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t id = next_id(kd);
    pending_op* op = insert_op(kd, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_WRITE;
    op->fd = fd;
    op->buf = (char*)malloc((size_t)len);
    if (!op->buf) { remove_op(kd, id); return -ENOMEM; }
    memcpy(op->buf, data, (size_t)len);
    op->buf_len = len;
    op->offset = offset;
    return id;
}

static int64_t kq_submit_open(spl_driver* d, const char* path,
                               int64_t flags, int64_t mode) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t id = next_id(kd);
    pending_op* op = insert_op(kd, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_OPEN;
    op->path = strdup(path);
    op->flags = flags;
    op->mode = mode;
    return id;
}

static int64_t kq_submit_close(spl_driver* d, int64_t fd) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t id = next_id(kd);
    pending_op* op = insert_op(kd, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_CLOSE;
    op->fd = fd;
    return id;
}

static int64_t kq_submit_fsync(spl_driver* d, int64_t fd) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t id = next_id(kd);
    pending_op* op = insert_op(kd, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_FSYNC;
    op->fd = fd;
    return id;
}

static int64_t kq_submit_timeout(spl_driver* d, int64_t timeout_ms) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t id = next_id(kd);
    pending_op* op = insert_op(kd, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_TIMEOUT;
    op->timeout_ms = timeout_ms;
    return id;
}

/* ================================================================
 * Flush — push queued ops to kqueue or threadpool
 * ================================================================ */

static int64_t kq_flush(spl_driver* d) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t submitted = 0;

    for (int64_t i = 0; i < kd->ops_cap; i++) {
        pending_op* op = &kd->ops[i];
        if (op->op_id == 0 || op->submitted || op->completed) continue;

        switch (op->op_type) {
        case OP_ACCEPT: {
            struct kevent ev;
            EV_SET(&ev, (uintptr_t)op->fd, EVFILT_READ, EV_ADD | EV_ONESHOT,
                   0, 0, (void*)(intptr_t)op->op_id);
            kevent(kd->kq_fd, &ev, 1, NULL, 0, NULL);
            op->submitted = 1;
            submitted++;
            break;
        }
        case OP_CONNECT: {
            struct sockaddr_in sa;
            memset(&sa, 0, sizeof(sa));
            sa.sin_family = AF_INET;
            sa.sin_port = htons((uint16_t)op->port);
            inet_pton(AF_INET, op->addr, &sa.sin_addr);
            set_nonblocking((int)op->fd);
            int rc = connect((int)op->fd, (struct sockaddr*)&sa, sizeof(sa));
            if (rc == 0) {
                op->result = 0;
                op->completed = 1;
            } else if (errno == EINPROGRESS) {
                struct kevent ev;
                EV_SET(&ev, (uintptr_t)op->fd, EVFILT_WRITE,
                       EV_ADD | EV_ONESHOT, 0, 0, (void*)(intptr_t)op->op_id);
                kevent(kd->kq_fd, &ev, 1, NULL, 0, NULL);
            } else {
                op->result = -errno;
                op->completed = 1;
            }
            op->submitted = 1;
            submitted++;
            break;
        }
        case OP_RECV: {
            struct kevent ev;
            EV_SET(&ev, (uintptr_t)op->fd, EVFILT_READ, EV_ADD | EV_ONESHOT,
                   0, 0, (void*)(intptr_t)op->op_id);
            kevent(kd->kq_fd, &ev, 1, NULL, 0, NULL);
            op->submitted = 1;
            submitted++;
            break;
        }
        case OP_SEND: {
            struct kevent ev;
            EV_SET(&ev, (uintptr_t)op->fd, EVFILT_WRITE, EV_ADD | EV_ONESHOT,
                   0, 0, (void*)(intptr_t)op->op_id);
            kevent(kd->kq_fd, &ev, 1, NULL, 0, NULL);
            op->submitted = 1;
            submitted++;
            break;
        }
        case OP_SENDFILE: {
            struct kevent ev;
            EV_SET(&ev, (uintptr_t)op->sock_fd, EVFILT_WRITE,
                   EV_ADD | EV_ONESHOT, 0, 0, (void*)(intptr_t)op->op_id);
            kevent(kd->kq_fd, &ev, 1, NULL, 0, NULL);
            op->submitted = 1;
            submitted++;
            break;
        }
        case OP_TIMEOUT: {
            struct kevent ev;
            EV_SET(&ev, (uintptr_t)op->op_id, EVFILT_TIMER,
                   EV_ADD | EV_ONESHOT, 0, (intptr_t)op->timeout_ms,
                   (void*)(intptr_t)op->op_id);
            kevent(kd->kq_fd, &ev, 1, NULL, 0, NULL);
            op->submitted = 1;
            submitted++;
            break;
        }
        /* File I/O goes to threadpool */
        case OP_READ:
        case OP_WRITE:
        case OP_OPEN:
        case OP_CLOSE:
        case OP_FSYNC: {
            pthread_mutex_lock(&kd->work_mutex);
            kd->work_queue[kd->work_tail % kd->work_cap] = op;
            kd->work_tail++;
            pthread_cond_signal(&kd->work_cond);
            pthread_mutex_unlock(&kd->work_mutex);
            op->submitted = 1;
            submitted++;
            break;
        }
        default:
            break;
        }
    }
    return submitted;
}

/* ================================================================
 * Poll — harvest completions from kqueue + done_queue
 * ================================================================ */

static int64_t kq_poll(spl_driver* d, spl_completion* out, int64_t max,
                        int64_t timeout_ms) {
    kqueue_driver* kd = (kqueue_driver*)d;
    int64_t count = 0;

    /* 1. Drain threadpool done_queue first */
    pthread_mutex_lock(&kd->done_mutex);
    while (kd->done_head != kd->done_tail && count < max) {
        out[count] = kd->done_queue[kd->done_head % kd->done_cap];
        kd->done_head++;
        count++;
    }
    pthread_mutex_unlock(&kd->done_mutex);

    /* 2. Also drain any already-completed ops (e.g. immediate connect) */
    for (int64_t i = 0; i < kd->ops_cap && count < max; i++) {
        pending_op* op = &kd->ops[i];
        if (op->op_id != 0 && op->completed) {
            out[count++] = (spl_completion){
                .id = op->op_id, .result = op->result, .flags = 0
            };
            remove_op(kd, op->op_id);
        }
    }

    if (count > 0 && timeout_ms == 0) return count;

    /* 3. Poll kqueue */
    struct timespec ts;
    struct timespec* ts_ptr = NULL;
    if (timeout_ms == 0) {
        ts = (struct timespec){0, 0};
        ts_ptr = &ts;
    } else if (timeout_ms > 0) {
        ts.tv_sec = timeout_ms / 1000;
        ts.tv_nsec = (timeout_ms % 1000) * 1000000L;
        ts_ptr = &ts;
    }
    /* timeout_ms == -1 means block forever: ts_ptr stays NULL */

    int64_t kq_max = max - count;
    if (kq_max <= 0) return count;

    struct kevent* events = (struct kevent*)malloc(sizeof(struct kevent) * (size_t)kq_max);
    if (!events) return count;

    int n = kevent(kd->kq_fd, NULL, 0, events, (int)kq_max, ts_ptr);

    for (int i = 0; i < n && count < max; i++) {
        int64_t op_id = (int64_t)(intptr_t)events[i].udata;
        pending_op* op = find_op(kd, op_id);
        if (!op) continue;

        switch (op->op_type) {
        case OP_ACCEPT: {
            struct sockaddr_in client;
            socklen_t clen = sizeof(client);
            int client_fd = accept((int)op->fd, (struct sockaddr*)&client, &clen);
            if (client_fd >= 0) {
                set_nonblocking(client_fd);
                op->result = client_fd;
            } else {
                op->result = -errno;
            }
            break;
        }
        case OP_CONNECT: {
            int err = 0;
            socklen_t elen = sizeof(err);
            getsockopt((int)op->fd, SOL_SOCKET, SO_ERROR, &err, &elen);
            op->result = err ? -err : 0;
            break;
        }
        case OP_RECV: {
            op->buf = (char*)malloc((size_t)op->buf_len);
            if (!op->buf) { op->result = -ENOMEM; break; }
            ssize_t r = recv((int)op->fd, op->buf, (size_t)op->buf_len, 0);
            op->result = (r >= 0) ? r : -errno;
            break;
        }
        case OP_SEND: {
            ssize_t r = send((int)op->fd, op->buf, (size_t)op->buf_len, 0);
            op->result = (r >= 0) ? r : -errno;
            break;
        }
        case OP_SENDFILE: {
            off_t sent_len = (off_t)op->buf_len;
            /* macOS sendfile: sendfile(fd, s, offset, &len, hdtr, flags) */
            int rc = sendfile((int)op->file_fd, (int)op->sock_fd,
                              (off_t)op->offset, &sent_len, NULL, 0);
            if (rc == 0 || (rc == -1 && errno == EAGAIN)) {
                op->result = (int64_t)sent_len;
            } else {
                op->result = -errno;
            }
            break;
        }
        case OP_TIMEOUT:
            op->result = 0;   /* timer fired successfully */
            break;
        default:
            op->result = -ENOTSUP;
            break;
        }

        out[count++] = (spl_completion){
            .id = op->op_id, .result = op->result, .flags = 0
        };
        remove_op(kd, op_id);
    }

    free(events);
    return count;
}

/* ================================================================
 * Cancel
 * ================================================================ */

static bool kq_cancel(spl_driver* d, int64_t op_id) {
    kqueue_driver* kd = (kqueue_driver*)d;
    pending_op* op = find_op(kd, op_id);
    if (!op) return false;

    /* Remove kqueue filter if network op */
    if (op->op_type == OP_ACCEPT || op->op_type == OP_RECV) {
        struct kevent ev;
        EV_SET(&ev, (uintptr_t)op->fd, EVFILT_READ, EV_DELETE, 0, 0, NULL);
        kevent(kd->kq_fd, &ev, 1, NULL, 0, NULL);
    } else if (op->op_type == OP_CONNECT || op->op_type == OP_SEND ||
               op->op_type == OP_SENDFILE) {
        struct kevent ev;
        int cancel_fd = (op->op_type == OP_SENDFILE) ? (int)op->sock_fd : (int)op->fd;
        EV_SET(&ev, (uintptr_t)cancel_fd, EVFILT_WRITE, EV_DELETE, 0, 0, NULL);
        kevent(kd->kq_fd, &ev, 1, NULL, 0, NULL);
    } else if (op->op_type == OP_TIMEOUT) {
        struct kevent ev;
        EV_SET(&ev, (uintptr_t)op->op_id, EVFILT_TIMER, EV_DELETE, 0, 0, NULL);
        kevent(kd->kq_fd, &ev, 1, NULL, 0, NULL);
    }

    remove_op(kd, op_id);
    return true;
}

/* ================================================================
 * Query
 * ================================================================ */

static const char* kq_backend_name(spl_driver* d) {
    (void)d;
    return "kqueue";
}

static spl_backend_type kq_backend_type_fn(spl_driver* d) {
    (void)d;
    return SPL_BACKEND_KQUEUE;
}

static bool kq_supports_sendfile(spl_driver* d) {
    (void)d;
    return true;
}

static bool kq_supports_zero_copy(spl_driver* d) {
    (void)d;
    return false;
}

/* ================================================================
 * VTable
 * ================================================================ */

static const spl_driver_vtable kqueue_vtable = {
    .destroy          = kq_destroy,
    .submit_accept    = kq_submit_accept,
    .submit_connect   = kq_submit_connect,
    .submit_recv      = kq_submit_recv,
    .submit_send      = kq_submit_send,
    .submit_sendfile  = kq_submit_sendfile,
    .submit_read      = kq_submit_read,
    .submit_write     = kq_submit_write,
    .submit_open      = kq_submit_open,
    .submit_close     = kq_submit_close,
    .submit_fsync     = kq_submit_fsync,
    .submit_timeout   = kq_submit_timeout,
    .flush            = kq_flush,
    .poll             = kq_poll,
    .cancel           = kq_cancel,
    .backend_name     = kq_backend_name,
    .backend_type_fn  = kq_backend_type_fn,
    .supports_sendfile = kq_supports_sendfile,
    .supports_zero_copy = kq_supports_zero_copy,
};

/* ================================================================
 * Constructor
 * ================================================================ */

#define DEFAULT_POOL_SIZE 4

spl_driver* spl_driver_create_kqueue(int64_t queue_depth) {
    if (queue_depth <= 0) queue_depth = 256;

    int kq = kqueue();
    if (kq < 0) return NULL;

    kqueue_driver* kd = (kqueue_driver*)calloc(1, sizeof(kqueue_driver));
    if (!kd) { close(kq); return NULL; }

    kd->base.vtable = &kqueue_vtable;
    kd->base.next_op_id = 0;
    kd->kq_fd = kq;

    /* hash table */
    kd->ops_cap = queue_depth * 2;
    kd->ops = (pending_op*)calloc((size_t)kd->ops_cap, sizeof(pending_op));
    if (!kd->ops) { close(kq); free(kd); return NULL; }
    kd->ops_count = 0;

    /* work queue */
    kd->work_cap = queue_depth;
    kd->work_queue = (pending_op**)calloc((size_t)kd->work_cap, sizeof(pending_op*));
    if (!kd->work_queue) { free(kd->ops); close(kq); free(kd); return NULL; }
    kd->work_head = 0;
    kd->work_tail = 0;

    /* done queue */
    kd->done_cap = queue_depth;
    kd->done_queue = (spl_completion*)calloc((size_t)kd->done_cap, sizeof(spl_completion));
    if (!kd->done_queue) {
        free(kd->work_queue); free(kd->ops); close(kq); free(kd);
        return NULL;
    }
    kd->done_head = 0;
    kd->done_tail = 0;

    pthread_mutex_init(&kd->work_mutex, NULL);
    pthread_cond_init(&kd->work_cond, NULL);
    pthread_mutex_init(&kd->done_mutex, NULL);
    kd->shutdown = 0;

    /* threadpool */
    kd->pool_size = DEFAULT_POOL_SIZE;
    kd->pool_threads = (pthread_t*)malloc(sizeof(pthread_t) * (size_t)kd->pool_size);
    if (!kd->pool_threads) {
        pthread_mutex_destroy(&kd->work_mutex);
        pthread_cond_destroy(&kd->work_cond);
        pthread_mutex_destroy(&kd->done_mutex);
        free(kd->done_queue); free(kd->work_queue); free(kd->ops);
        close(kq); free(kd);
        return NULL;
    }
    for (int i = 0; i < kd->pool_size; i++)
        pthread_create(&kd->pool_threads[i], NULL, threadpool_worker, kd);

    return (spl_driver*)kd;
}

#endif /* defined(__APPLE__) */
