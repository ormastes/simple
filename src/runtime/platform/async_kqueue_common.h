/*
 * Shared kqueue driver helpers for async_freebsd.c and async_macos.c.
 *
 * Not a standalone header: include it from a kqueue backend .c file AFTER it
 * defines the OP_* constants, `pending_op` (with op_id, op_type, fd, buf,
 * buf_len, offset, path, flags, mode, sock_fd, file_fd, timeout_ms, addr,
 * port) and `kqueue_driver` (with base, ops, ops_cap, ops_count).
 * Provides the pending-op hash table, next_id/set_nonblocking, and every
 * kq_submit_* except kq_submit_read (backend-specific buffer ownership).
 */
#ifndef SPL_ASYNC_KQUEUE_COMMON_H
#define SPL_ASYNC_KQUEUE_COMMON_H

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
 * Helpers
 * ================================================================ */

static int64_t next_id(kqueue_driver* kd) {
    return ++kd->base.next_op_id;
}

static void set_nonblocking(int fd) {
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags >= 0) fcntl(fd, F_SETFL, flags | O_NONBLOCK);
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


#endif /* SPL_ASYNC_KQUEUE_COMMON_H */
