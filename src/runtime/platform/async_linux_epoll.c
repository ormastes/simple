/*
 * Linux epoll backend for spl_driver
 *
 * Emulates a completion-based (proactor) API on top of epoll's readiness model.
 * Network operations are dispatched directly via epoll_wait + syscall on ready.
 * File I/O operations (open, read, write, close, fsync) are offloaded to a
 * small threadpool because regular files are not meaningfully pollable by epoll.
 * Timeouts use timerfd for seamless integration with the epoll event loop.
 *
 * See async_driver.h for the interface contract.
 */

#if defined(__linux__)

/* Required for pread/pwrite, strdup, accept4, SOCK_NONBLOCK, etc. */
#define _GNU_SOURCE

#include "async_driver.h"

#include <sys/epoll.h>
#include <sys/timerfd.h>
#include <sys/sendfile.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <time.h>
#include <sched.h>

/* Forward declarations for SplArray (defined in runtime.h / runtime.c) */
typedef struct SplArray SplArray;
SplArray* spl_array_new_i64(void);
void      spl_array_push_i64(SplArray* a, int64_t n);

/* ===== Internal Constants ===== */

#define EPOLL_MAX_EVENTS  256
#define HASH_LOAD_LIMIT   70   /* percent — rehash above this */

/* ===== Op Types ===== */

enum {
    OP_ACCEPT   = 1,
    OP_CONNECT  = 2,
    OP_RECV     = 3,
    OP_SEND     = 4,
    OP_SENDFILE = 5,
    OP_READ     = 6,
    OP_WRITE    = 7,
    OP_OPEN     = 8,
    OP_CLOSE    = 9,
    OP_FSYNC    = 10,
    OP_TIMEOUT  = 11
};

/* ===== Pending Operation ===== */

typedef struct pending_op {
    int64_t  op_id;       /* 0 = empty slot, -1 = tombstone */
    int      op_type;
    int      fd;
    char*    buf;         /* heap-allocated for recv/read results */
    int64_t  buf_len;
    int64_t  offset;
    char*    path;        /* strdup'd for open */
    char*    addr;        /* strdup'd for connect */
    int64_t  port;
    int64_t  flags;
    int64_t  mode;
    int64_t  timeout_ms;
    int      file_fd;     /* source fd for sendfile */
    int      timerfd;     /* fd from timerfd_create, -1 if unused */
} pending_op;

/* ===== Driver Structure ===== */

typedef struct {
    spl_driver      base;
    int             epoll_fd;

    /* Open-addressing hash table of pending ops (keyed by op_id) */
    pending_op*     ops;
    int64_t         ops_cap;
    int64_t         ops_count;

    /* Threadpool for file I/O */
    pthread_t*      pool_threads;
    int             pool_size;

    /* Work queue: pending ops pushed here for pool threads */
    pending_op**    work_queue;
    int64_t         work_head;
    int64_t         work_tail;
    int64_t         work_cap;
    pthread_mutex_t work_mutex;
    pthread_cond_t  work_cond;

    /* Done queue: completed file-I/O results */
    spl_completion* done_queue;
    int64_t         done_head;
    int64_t         done_tail;
    int64_t         done_cap;
    pthread_mutex_t done_mutex;

    volatile int    shutdown;
} epoll_driver;

/* ===== Hash Table Helpers ===== */

static inline int64_t hash_id(int64_t id, int64_t cap) {
    /* Fibonacci hashing */
    uint64_t h = (uint64_t)id * 11400714819323198485ULL;
    return (int64_t)(h >> (64 - 20)) & (cap - 1);  /* cap is power-of-2 */
}

static pending_op* map_find(epoll_driver* ed, int64_t op_id) {
    int64_t idx = hash_id(op_id, ed->ops_cap);
    for (int64_t i = 0; i < ed->ops_cap; i++) {
        pending_op* slot = &ed->ops[(idx + i) & (ed->ops_cap - 1)];
        if (slot->op_id == 0) return NULL;         /* empty — not found */
        if (slot->op_id == op_id) return slot;      /* found */
        /* tombstone (-1) or collision — keep probing */
    }
    return NULL;
}

static pending_op* map_find_by_fd(epoll_driver* ed, int fd, int op_type) {
    for (int64_t i = 0; i < ed->ops_cap; i++) {
        pending_op* slot = &ed->ops[i];
        if (slot->op_id > 0 && slot->fd == fd && slot->op_type == op_type)
            return slot;
    }
    return NULL;
}

static pending_op* map_find_by_timerfd(epoll_driver* ed, int tfd) {
    for (int64_t i = 0; i < ed->ops_cap; i++) {
        pending_op* slot = &ed->ops[i];
        if (slot->op_id > 0 && slot->timerfd == tfd)
            return slot;
    }
    return NULL;
}

static void map_rehash(epoll_driver* ed);

static pending_op* map_insert(epoll_driver* ed, int64_t op_id) {
    if (ed->ops_count * 100 / ed->ops_cap >= HASH_LOAD_LIMIT) {
        map_rehash(ed);
    }
    int64_t idx = hash_id(op_id, ed->ops_cap);
    for (int64_t i = 0; i < ed->ops_cap; i++) {
        pending_op* slot = &ed->ops[(idx + i) & (ed->ops_cap - 1)];
        if (slot->op_id <= 0) {  /* empty (0) or tombstone (-1) */
            memset(slot, 0, sizeof(*slot));
            slot->op_id  = op_id;
            slot->timerfd = -1;
            ed->ops_count++;
            return slot;
        }
    }
    /* Should never reach here if load factor is maintained */
    return NULL;
}

static void map_remove(epoll_driver* ed, pending_op* op) {
    if (op->path)  { free(op->path);  op->path = NULL; }
    if (op->addr)  { free(op->addr);  op->addr = NULL; }
    if (op->buf)   { free(op->buf);   op->buf  = NULL; }
    op->op_id = -1;  /* tombstone */
    ed->ops_count--;
}

static void map_rehash(epoll_driver* ed) {
    int64_t old_cap = ed->ops_cap;
    pending_op* old_ops = ed->ops;

    int64_t new_cap = old_cap * 2;
    pending_op* new_ops = (pending_op*)calloc((size_t)new_cap, sizeof(pending_op));
    if (!new_ops) return;  /* out of memory — keep old table */

    ed->ops       = new_ops;
    ed->ops_cap   = new_cap;
    ed->ops_count = 0;

    for (int64_t i = 0; i < old_cap; i++) {
        if (old_ops[i].op_id > 0) {
            pending_op* dst = map_insert(ed, old_ops[i].op_id);
            if (dst) {
                int64_t saved_id = dst->op_id;
                *dst = old_ops[i];
                dst->op_id = saved_id;
            }
        }
    }
    free(old_ops);
}

/* ===== Threadpool Worker ===== */

static void* pool_worker(void* arg) {
    epoll_driver* ed = (epoll_driver*)arg;

    while (1) {
        pthread_mutex_lock(&ed->work_mutex);
        while (ed->work_head == ed->work_tail && !ed->shutdown) {
            pthread_cond_wait(&ed->work_cond, &ed->work_mutex);
        }
        if (ed->shutdown && ed->work_head == ed->work_tail) {
            pthread_mutex_unlock(&ed->work_mutex);
            break;
        }
        pending_op* op = ed->work_queue[ed->work_head & (ed->work_cap - 1)];
        ed->work_head++;
        pthread_mutex_unlock(&ed->work_mutex);

        /* Execute the file I/O syscall */
        spl_completion c;
        c.id    = op->op_id;
        c.flags = 0;

        switch (op->op_type) {
        case OP_OPEN: {
            int fd = open(op->path, (int)op->flags, (mode_t)op->mode);
            c.result = (fd >= 0) ? fd : -errno;
            break;
        }
        case OP_READ: {
            ssize_t n = pread(op->fd, op->buf, (size_t)op->buf_len, (off_t)op->offset);
            c.result = (n >= 0) ? n : -errno;
            break;
        }
        case OP_WRITE: {
            ssize_t n = pwrite(op->fd, op->buf, (size_t)op->buf_len, (off_t)op->offset);
            c.result = (n >= 0) ? n : -errno;
            break;
        }
        case OP_CLOSE: {
            int rc = close(op->fd);
            c.result = (rc == 0) ? 0 : -errno;
            break;
        }
        case OP_FSYNC: {
            int rc = fsync(op->fd);
            c.result = (rc == 0) ? 0 : -errno;
            break;
        }
        default:
            c.result = -ENOTSUP;
            break;
        }

        /* Push completion onto done queue */
        pthread_mutex_lock(&ed->done_mutex);
        ed->done_queue[ed->done_tail & (ed->done_cap - 1)] = c;
        ed->done_tail++;
        pthread_mutex_unlock(&ed->done_mutex);
    }
    return NULL;
}

static void pool_submit(epoll_driver* ed, pending_op* op) {
    pthread_mutex_lock(&ed->work_mutex);
    ed->work_queue[ed->work_tail & (ed->work_cap - 1)] = op;
    ed->work_tail++;
    pthread_cond_signal(&ed->work_cond);
    pthread_mutex_unlock(&ed->work_mutex);
}

/* ===== Helper: next op_id ===== */

static int64_t next_id(epoll_driver* ed) {
    return ++ed->base.next_op_id;
}

/* ===== Helper: set fd non-blocking ===== */

static int set_nonblocking(int fd) {
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags < 0) return -errno;
    if (fcntl(fd, F_SETFL, flags | O_NONBLOCK) < 0) return -errno;
    return 0;
}

/* ===== vtable Implementations ===== */

static void ep_destroy(spl_driver* d) {
    epoll_driver* ed = (epoll_driver*)d;

    /* Signal threadpool shutdown */
    pthread_mutex_lock(&ed->work_mutex);
    ed->shutdown = 1;
    pthread_cond_broadcast(&ed->work_cond);
    pthread_mutex_unlock(&ed->work_mutex);

    for (int i = 0; i < ed->pool_size; i++) {
        pthread_join(ed->pool_threads[i], NULL);
    }
    free(ed->pool_threads);

    /* Clean up pending ops */
    for (int64_t i = 0; i < ed->ops_cap; i++) {
        pending_op* op = &ed->ops[i];
        if (op->op_id > 0) {
            if (op->timerfd >= 0) close(op->timerfd);
            free(op->path);
            free(op->addr);
            free(op->buf);
        }
    }
    free(ed->ops);

    /* Destroy synchronization */
    pthread_mutex_destroy(&ed->work_mutex);
    pthread_cond_destroy(&ed->work_cond);
    pthread_mutex_destroy(&ed->done_mutex);

    free(ed->work_queue);
    free(ed->done_queue);

    close(ed->epoll_fd);
    free(ed);
}

/* --- Network submit --- */

static int64_t ep_submit_accept(spl_driver* d, int64_t listen_fd) {
    epoll_driver* ed = (epoll_driver*)d;
    int64_t id = next_id(ed);

    pending_op* op = map_insert(ed, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_ACCEPT;
    op->fd      = (int)listen_fd;

    struct epoll_event ev;
    ev.events  = EPOLLIN;
    ev.data.fd = (int)listen_fd;
    epoll_ctl(ed->epoll_fd, EPOLL_CTL_ADD, (int)listen_fd, &ev);

    return id;
}

static int64_t ep_submit_connect(spl_driver* d, int64_t fd,
                                  const char* addr, int64_t port) {
    epoll_driver* ed = (epoll_driver*)d;
    int sfd = (int)fd;

    set_nonblocking(sfd);

    struct sockaddr_in sa;
    memset(&sa, 0, sizeof(sa));
    sa.sin_family = AF_INET;
    sa.sin_port   = htons((uint16_t)port);
    inet_pton(AF_INET, addr, &sa.sin_addr);

    int rc = connect(sfd, (struct sockaddr*)&sa, sizeof(sa));
    if (rc < 0 && errno != EINPROGRESS) {
        return -errno;
    }

    int64_t id = next_id(ed);
    pending_op* op = map_insert(ed, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_CONNECT;
    op->fd      = sfd;
    op->addr    = strdup(addr);
    op->port    = port;

    struct epoll_event ev;
    ev.events  = EPOLLOUT;
    ev.data.fd = sfd;
    epoll_ctl(ed->epoll_fd, EPOLL_CTL_ADD, sfd, &ev);

    return id;
}

static int64_t ep_submit_recv(spl_driver* d, int64_t fd, int64_t buf_size) {
    epoll_driver* ed = (epoll_driver*)d;
    int64_t id = next_id(ed);

    pending_op* op = map_insert(ed, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_RECV;
    op->fd      = (int)fd;
    op->buf     = (char*)malloc((size_t)buf_size);
    op->buf_len = buf_size;
    if (!op->buf) { map_remove(ed, op); return -ENOMEM; }

    struct epoll_event ev;
    ev.events  = EPOLLIN;
    ev.data.fd = (int)fd;
    epoll_ctl(ed->epoll_fd, EPOLL_CTL_MOD, (int)fd, &ev);
    if (errno == ENOENT) {
        epoll_ctl(ed->epoll_fd, EPOLL_CTL_ADD, (int)fd, &ev);
    }

    return id;
}

static int64_t ep_submit_send(spl_driver* d, int64_t fd,
                               const char* data, int64_t len) {
    epoll_driver* ed = (epoll_driver*)d;
    int64_t id = next_id(ed);

    pending_op* op = map_insert(ed, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_SEND;
    op->fd      = (int)fd;
    op->buf     = (char*)malloc((size_t)len);
    op->buf_len = len;
    if (!op->buf) { map_remove(ed, op); return -ENOMEM; }
    memcpy(op->buf, data, (size_t)len);

    struct epoll_event ev;
    ev.events  = EPOLLOUT;
    ev.data.fd = (int)fd;
    epoll_ctl(ed->epoll_fd, EPOLL_CTL_MOD, (int)fd, &ev);
    if (errno == ENOENT) {
        epoll_ctl(ed->epoll_fd, EPOLL_CTL_ADD, (int)fd, &ev);
    }

    return id;
}

static int64_t ep_submit_sendfile(spl_driver* d, int64_t sock_fd,
                                   int64_t file_fd,
                                   int64_t offset, int64_t len) {
    epoll_driver* ed = (epoll_driver*)d;
    int64_t id = next_id(ed);

    pending_op* op = map_insert(ed, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_SENDFILE;
    op->fd      = (int)sock_fd;
    op->file_fd = (int)file_fd;
    op->offset  = offset;
    op->buf_len = len;

    struct epoll_event ev;
    ev.events  = EPOLLOUT;
    ev.data.fd = (int)sock_fd;
    epoll_ctl(ed->epoll_fd, EPOLL_CTL_MOD, (int)sock_fd, &ev);
    if (errno == ENOENT) {
        epoll_ctl(ed->epoll_fd, EPOLL_CTL_ADD, (int)sock_fd, &ev);
    }

    return id;
}

/* --- File I/O submit (offloaded to threadpool) --- */

static int64_t ep_submit_read(spl_driver* d, int64_t fd,
                               int64_t buf_size, int64_t offset) {
    epoll_driver* ed = (epoll_driver*)d;
    int64_t id = next_id(ed);

    pending_op* op = map_insert(ed, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_READ;
    op->fd      = (int)fd;
    op->buf     = (char*)malloc((size_t)buf_size);
    op->buf_len = buf_size;
    op->offset  = offset;
    if (!op->buf) { map_remove(ed, op); return -ENOMEM; }

    pool_submit(ed, op);
    return id;
}

static int64_t ep_submit_write(spl_driver* d, int64_t fd,
                                const char* data, int64_t len, int64_t offset) {
    epoll_driver* ed = (epoll_driver*)d;
    int64_t id = next_id(ed);

    pending_op* op = map_insert(ed, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_WRITE;
    op->fd      = (int)fd;
    op->buf     = (char*)malloc((size_t)len);
    op->buf_len = len;
    op->offset  = offset;
    if (!op->buf) { map_remove(ed, op); return -ENOMEM; }
    memcpy(op->buf, data, (size_t)len);

    pool_submit(ed, op);
    return id;
}

static int64_t ep_submit_open(spl_driver* d, const char* path,
                               int64_t flags, int64_t mode) {
    epoll_driver* ed = (epoll_driver*)d;
    int64_t id = next_id(ed);

    pending_op* op = map_insert(ed, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_OPEN;
    op->path    = strdup(path);
    op->flags   = flags;
    op->mode    = mode;
    if (!op->path) { map_remove(ed, op); return -ENOMEM; }

    pool_submit(ed, op);
    return id;
}

static int64_t ep_submit_close(spl_driver* d, int64_t fd) {
    epoll_driver* ed = (epoll_driver*)d;
    int64_t id = next_id(ed);

    pending_op* op = map_insert(ed, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_CLOSE;
    op->fd      = (int)fd;

    pool_submit(ed, op);
    return id;
}

static int64_t ep_submit_fsync(spl_driver* d, int64_t fd) {
    epoll_driver* ed = (epoll_driver*)d;
    int64_t id = next_id(ed);

    pending_op* op = map_insert(ed, id);
    if (!op) return -ENOMEM;
    op->op_type = OP_FSYNC;
    op->fd      = (int)fd;

    pool_submit(ed, op);
    return id;
}

/* --- Timer --- */

static int64_t ep_submit_timeout(spl_driver* d, int64_t timeout_ms) {
    epoll_driver* ed = (epoll_driver*)d;

    int tfd = timerfd_create(CLOCK_MONOTONIC, TFD_NONBLOCK | TFD_CLOEXEC);
    if (tfd < 0) return -errno;

    struct itimerspec ts;
    memset(&ts, 0, sizeof(ts));
    ts.it_value.tv_sec  = timeout_ms / 1000;
    ts.it_value.tv_nsec = (timeout_ms % 1000) * 1000000L;
    /* One-shot: it_interval stays zero */

    if (timerfd_settime(tfd, 0, &ts, NULL) < 0) {
        int err = errno;
        close(tfd);
        return -err;
    }

    int64_t id = next_id(ed);
    pending_op* op = map_insert(ed, id);
    if (!op) { close(tfd); return -ENOMEM; }
    op->op_type    = OP_TIMEOUT;
    op->timerfd    = tfd;
    op->timeout_ms = timeout_ms;

    struct epoll_event ev;
    ev.events  = EPOLLIN;
    ev.data.fd = tfd;
    epoll_ctl(ed->epoll_fd, EPOLL_CTL_ADD, tfd, &ev);

    return id;
}

/* --- Batch control --- */

static int64_t ep_flush(spl_driver* d) {
    (void)d;
    /* epoll operations are registered immediately in submit_*; nothing to flush. */
    return 0;
}

/* --- Poll --- */

static int64_t ep_poll(spl_driver* d, spl_completion* out,
                        int64_t max, int64_t timeout_ms) {
    epoll_driver* ed = (epoll_driver*)d;
    int64_t count = 0;

    /* 1. Drain completed file I/O from done_queue */
    pthread_mutex_lock(&ed->done_mutex);
    while (ed->done_head != ed->done_tail && count < max) {
        spl_completion c = ed->done_queue[ed->done_head & (ed->done_cap - 1)];
        ed->done_head++;
        out[count++] = c;
    }
    pthread_mutex_unlock(&ed->done_mutex);

    /* Remove file-I/O ops that completed from the pending map */
    for (int64_t i = 0; i < count; i++) {
        pending_op* op = map_find(ed, out[i].id);
        if (op) map_remove(ed, op);
    }

    if (count >= max) return count;

    /* 2. epoll_wait for network/timer completions */
    int epoll_timeout;
    if (count > 0) {
        epoll_timeout = 0;  /* already have results, don't block */
    } else if (timeout_ms < 0) {
        epoll_timeout = -1;
    } else {
        epoll_timeout = (int)timeout_ms;
    }

    struct epoll_event events[EPOLL_MAX_EVENTS];
    int remaining = (int)(max - count);
    if (remaining > EPOLL_MAX_EVENTS) remaining = EPOLL_MAX_EVENTS;

    int nfds = epoll_wait(ed->epoll_fd, events, remaining, epoll_timeout);
    if (nfds < 0) {
        if (errno == EINTR) return count;
        return (count > 0) ? count : -errno;
    }

    for (int i = 0; i < nfds && count < max; i++) {
        int fd = events[i].data.fd;
        uint32_t ev = events[i].events;
        spl_completion c;
        c.flags = 0;

        /* Check if this is a timerfd */
        pending_op* top = map_find_by_timerfd(ed, fd);
        if (top) {
            uint64_t expirations;
            ssize_t r = read(fd, &expirations, sizeof(expirations));
            (void)r;
            c.id     = top->op_id;
            c.result = 0;  /* timeout completed successfully */
            epoll_ctl(ed->epoll_fd, EPOLL_CTL_DEL, fd, NULL);
            close(fd);
            map_remove(ed, top);
            out[count++] = c;
            continue;
        }

        /* Check for accept */
        pending_op* aop = map_find_by_fd(ed, fd, OP_ACCEPT);
        if (aop && (ev & EPOLLIN)) {
            struct sockaddr_in peer;
            socklen_t plen = sizeof(peer);
            int client = accept4(fd, (struct sockaddr*)&peer, &plen,
                                  SOCK_NONBLOCK | SOCK_CLOEXEC);
            c.id     = aop->op_id;
            c.result = (client >= 0) ? client : -errno;
            /* Keep listening: re-register for next accept is caller's job */
            epoll_ctl(ed->epoll_fd, EPOLL_CTL_DEL, fd, NULL);
            map_remove(ed, aop);
            out[count++] = c;
            continue;
        }

        /* Check for connect */
        pending_op* cop = map_find_by_fd(ed, fd, OP_CONNECT);
        if (cop && (ev & EPOLLOUT)) {
            int err = 0;
            socklen_t elen = sizeof(err);
            getsockopt(fd, SOL_SOCKET, SO_ERROR, &err, &elen);
            c.id     = cop->op_id;
            c.result = (err == 0) ? 0 : -err;
            epoll_ctl(ed->epoll_fd, EPOLL_CTL_DEL, fd, NULL);
            map_remove(ed, cop);
            out[count++] = c;
            continue;
        }

        /* Check for recv */
        pending_op* rop = map_find_by_fd(ed, fd, OP_RECV);
        if (rop && (ev & EPOLLIN)) {
            ssize_t n = recv(fd, rop->buf, (size_t)rop->buf_len, 0);
            c.id     = rop->op_id;
            c.result = (n >= 0) ? n : -errno;
            epoll_ctl(ed->epoll_fd, EPOLL_CTL_DEL, fd, NULL);
            map_remove(ed, rop);
            out[count++] = c;
            continue;
        }

        /* Check for send */
        pending_op* sop = map_find_by_fd(ed, fd, OP_SEND);
        if (sop && (ev & EPOLLOUT)) {
            ssize_t n = send(fd, sop->buf, (size_t)sop->buf_len, MSG_NOSIGNAL);
            c.id     = sop->op_id;
            c.result = (n >= 0) ? n : -errno;
            epoll_ctl(ed->epoll_fd, EPOLL_CTL_DEL, fd, NULL);
            map_remove(ed, sop);
            out[count++] = c;
            continue;
        }

        /* Check for sendfile */
        pending_op* sfop = map_find_by_fd(ed, fd, OP_SENDFILE);
        if (sfop && (ev & EPOLLOUT)) {
            off_t off = (off_t)sfop->offset;
            ssize_t n = sendfile(fd, sfop->file_fd, &off, (size_t)sfop->buf_len);
            c.id     = sfop->op_id;
            c.result = (n >= 0) ? n : -errno;
            epoll_ctl(ed->epoll_fd, EPOLL_CTL_DEL, fd, NULL);
            map_remove(ed, sfop);
            out[count++] = c;
            continue;
        }

        /* EPOLLERR / EPOLLHUP with no matching op — stale fd, remove */
        if (ev & (EPOLLERR | EPOLLHUP)) {
            epoll_ctl(ed->epoll_fd, EPOLL_CTL_DEL, fd, NULL);
        }
    }

    return count;
}

/* --- Cancel --- */

static bool ep_cancel(spl_driver* d, int64_t op_id) {
    epoll_driver* ed = (epoll_driver*)d;
    pending_op* op = map_find(ed, op_id);
    if (!op) return false;

    /* Remove from epoll if it's a network op or timer */
    switch (op->op_type) {
    case OP_ACCEPT:
    case OP_CONNECT:
    case OP_RECV:
    case OP_SEND:
    case OP_SENDFILE:
        epoll_ctl(ed->epoll_fd, EPOLL_CTL_DEL, op->fd, NULL);
        break;
    case OP_TIMEOUT:
        if (op->timerfd >= 0) {
            epoll_ctl(ed->epoll_fd, EPOLL_CTL_DEL, op->timerfd, NULL);
            close(op->timerfd);
        }
        break;
    default:
        /* File I/O ops in the threadpool cannot be cancelled mid-flight,
         * but we mark them removed so their completion is discarded. */
        break;
    }

    map_remove(ed, op);
    return true;
}

/* --- Query --- */

static const char* ep_backend_name(spl_driver* d) {
    (void)d;
    return "epoll";
}

static spl_backend_type ep_backend_type_fn(spl_driver* d) {
    (void)d;
    return SPL_BACKEND_EPOLL;
}

static bool ep_supports_sendfile(spl_driver* d) {
    (void)d;
    return true;
}

static bool ep_supports_zero_copy(spl_driver* d) {
    (void)d;
    return false;
}

/* ===== vtable ===== */

static const spl_driver_vtable epoll_vtable = {
    .destroy           = ep_destroy,
    .submit_accept     = ep_submit_accept,
    .submit_connect    = ep_submit_connect,
    .submit_recv       = ep_submit_recv,
    .submit_send       = ep_submit_send,
    .submit_sendfile   = ep_submit_sendfile,
    .submit_read       = ep_submit_read,
    .submit_write      = ep_submit_write,
    .submit_open       = ep_submit_open,
    .submit_close      = ep_submit_close,
    .submit_fsync      = ep_submit_fsync,
    .submit_timeout    = ep_submit_timeout,
    .flush             = ep_flush,
    .poll              = ep_poll,
    .cancel            = ep_cancel,
    .backend_name      = ep_backend_name,
    .backend_type_fn   = ep_backend_type_fn,
    .supports_sendfile = ep_supports_sendfile,
    .supports_zero_copy = ep_supports_zero_copy
};

/* ===== Constructor ===== */

static int get_cpu_count(void) {
    int n = (int)sysconf(_SC_NPROCESSORS_ONLN);
    return (n > 0) ? n : 1;
}

spl_driver* spl_driver_create_epoll(int64_t queue_depth) {
    epoll_driver* ed = (epoll_driver*)calloc(1, sizeof(epoll_driver));
    if (!ed) return NULL;

    ed->base.vtable     = &epoll_vtable;
    ed->base.next_op_id = 0;

    ed->epoll_fd = epoll_create1(EPOLL_CLOEXEC);
    if (ed->epoll_fd < 0) {
        free(ed);
        return NULL;
    }

    /* Hash table — round queue_depth up to next power of 2, minimum 256 */
    int64_t cap = 256;
    while (cap < queue_depth * 2) cap *= 2;
    ed->ops = (pending_op*)calloc((size_t)cap, sizeof(pending_op));
    if (!ed->ops) {
        close(ed->epoll_fd);
        free(ed);
        return NULL;
    }
    ed->ops_cap   = cap;
    ed->ops_count = 0;

    /* Work queue for file I/O threadpool */
    ed->work_cap = (queue_depth > 64) ? queue_depth : 64;
    /* Round to power of 2 */
    {
        int64_t wc = 64;
        while (wc < ed->work_cap) wc *= 2;
        ed->work_cap = wc;
    }
    ed->work_queue = (pending_op**)calloc((size_t)ed->work_cap, sizeof(pending_op*));
    ed->work_head  = 0;
    ed->work_tail  = 0;
    pthread_mutex_init(&ed->work_mutex, NULL);
    pthread_cond_init(&ed->work_cond, NULL);

    /* Done queue for completed file I/O */
    ed->done_cap = ed->work_cap;
    ed->done_queue = (spl_completion*)calloc((size_t)ed->done_cap, sizeof(spl_completion));
    ed->done_head  = 0;
    ed->done_tail  = 0;
    pthread_mutex_init(&ed->done_mutex, NULL);

    if (!ed->work_queue || !ed->done_queue) {
        /* Partial init failure */
        free(ed->work_queue);
        free(ed->done_queue);
        free(ed->ops);
        close(ed->epoll_fd);
        free(ed);
        return NULL;
    }

    ed->shutdown = 0;

    /* Start threadpool: min(cpu_count, 8) workers */
    int ncpu = get_cpu_count();
    ed->pool_size = (ncpu < 8) ? ncpu : 8;
    ed->pool_threads = (pthread_t*)calloc((size_t)ed->pool_size, sizeof(pthread_t));
    if (!ed->pool_threads) {
        free(ed->work_queue);
        free(ed->done_queue);
        free(ed->ops);
        close(ed->epoll_fd);
        free(ed);
        return NULL;
    }
    for (int i = 0; i < ed->pool_size; i++) {
        if (pthread_create(&ed->pool_threads[i], NULL, pool_worker, ed) != 0) {
            /* Partial thread creation — shut down what we started */
            ed->shutdown = 1;
            pthread_cond_broadcast(&ed->work_cond);
            for (int j = 0; j < i; j++) {
                pthread_join(ed->pool_threads[j], NULL);
            }
            free(ed->pool_threads);
            free(ed->work_queue);
            free(ed->done_queue);
            free(ed->ops);
            close(ed->epoll_fd);
            free(ed);
            return NULL;
        }
    }

    return &ed->base;
}

/* ===== Legacy epoll FFI (used by event_loop.spl) ===== */

int64_t rt_epoll_create(void) {
    int fd = epoll_create1(EPOLL_CLOEXEC);
    return (fd >= 0) ? (int64_t)fd : -(int64_t)errno;
}

int64_t rt_epoll_ctl(int64_t epfd, int64_t op, int64_t fd, int64_t events) {
    struct epoll_event ev;
    ev.events  = (uint32_t)events;
    ev.data.fd = (int)fd;
    int rc = epoll_ctl((int)epfd, (int)op, (int)fd, &ev);
    return (rc == 0) ? 0 : -(int64_t)errno;
}

SplArray* rt_epoll_wait(int64_t epfd, int64_t max_events, int64_t timeout_ms) {
    SplArray* result = spl_array_new_i64();

    int n = (int)max_events;
    if (n > EPOLL_MAX_EVENTS) n = EPOLL_MAX_EVENTS;

    struct epoll_event events[EPOLL_MAX_EVENTS];
    int nfds = epoll_wait((int)epfd, events, n, (int)timeout_ms);

    for (int i = 0; i < nfds; i++) {
        spl_array_push_i64(result, (int64_t)events[i].data.fd);
        spl_array_push_i64(result, (int64_t)events[i].events);
    }

    return result;
}

bool rt_socket_set_nonblocking(int64_t fd, bool enabled) {
    int flags = fcntl((int)fd, F_GETFL, 0);
    if (flags < 0) return false;
    if (enabled) {
        flags |= O_NONBLOCK;
    } else {
        flags &= ~O_NONBLOCK;
    }
    return (fcntl((int)fd, F_SETFL, flags) == 0);
}

#endif /* defined(__linux__) */
