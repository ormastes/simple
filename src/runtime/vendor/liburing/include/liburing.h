/* SPDX-License-Identifier: MIT */
/*
 * liburing — userspace io_uring library
 * Vendored minimal subset for Simple's async I/O driver.
 *
 * Original: https://github.com/axboe/liburing (LGPL-2.1 OR MIT)
 *
 * This header provides the high-level API used by async_linux_uring.c.
 * The implementation is in src/setup.c, src/queue.c, src/register.c, src/syscall.c.
 */

#ifndef LIBURING_H
#define LIBURING_H

#ifdef __cplusplus
extern "C" {
#endif

#include <signal.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <stdint.h>
#include <stdbool.h>
#include <unistd.h>
#include <fcntl.h>

#include "liburing/compat.h"
#include "liburing/io_uring.h"
#include "liburing/barrier.h"

/*
 * Library API version
 */
#define IORING_VERSION_MAJOR 2
#define IORING_VERSION_MINOR 6

/*
 * Core io_uring ring structure
 */
struct io_uring_sq {
    unsigned *khead;
    unsigned *ktail;
    unsigned *kring_mask;
    unsigned *kring_entries;
    unsigned *kflags;
    unsigned *kdropped;
    unsigned *array;
    struct io_uring_sqe *sqes;

    unsigned sqe_head;
    unsigned sqe_tail;

    size_t ring_sz;
    void *ring_ptr;

    unsigned ring_mask;
    unsigned ring_entries;

    unsigned pad[2];
};

struct io_uring_cq {
    unsigned *khead;
    unsigned *ktail;
    unsigned *kring_mask;
    unsigned *kring_entries;
    unsigned *kflags;
    unsigned *koverflow;
    struct io_uring_cqe *cqes;

    size_t ring_sz;
    void *ring_ptr;

    unsigned ring_mask;
    unsigned ring_entries;

    unsigned pad[2];
};

struct io_uring {
    struct io_uring_sq sq;
    struct io_uring_cq cq;
    unsigned flags;
    int ring_fd;

    unsigned features;
    int enter_ring_fd;
    __u8 int_flags;
    __u8 pad[3];
    unsigned pad2;
};

/*
 * Library interface — setup/teardown
 */
int io_uring_queue_init(unsigned entries, struct io_uring *ring, unsigned flags);
int io_uring_queue_init_params(unsigned entries, struct io_uring *ring,
                               struct io_uring_params *p);
void io_uring_queue_exit(struct io_uring *ring);

/*
 * SQE helpers
 */
static inline struct io_uring_sqe *io_uring_get_sqe(struct io_uring *ring)
{
    struct io_uring_sq *sq = &ring->sq;
    unsigned int head, next;

    head = io_uring_smp_load_acquire(sq->khead);
    next = sq->sqe_tail + 1;

    if (next - head > sq->ring_entries)
        return NULL;

    struct io_uring_sqe *sqe = &sq->sqes[sq->sqe_tail & sq->ring_mask];
    sq->sqe_tail = next;
    return sqe;
}

/*
 * SQE prep helpers
 */
static inline void io_uring_sqe_set_data64(struct io_uring_sqe *sqe, __u64 data)
{
    sqe->user_data = data;
}

static inline void io_uring_sqe_set_flags(struct io_uring_sqe *sqe, unsigned flags)
{
    sqe->flags = (__u8)flags;
}

static inline void io_uring_prep_rw(int op, struct io_uring_sqe *sqe,
                                     int fd, const void *addr, unsigned len,
                                     __u64 offset)
{
    memset(sqe, 0, sizeof(*sqe));
    sqe->opcode = (__u8)op;
    sqe->fd = fd;
    sqe->off = offset;
    sqe->addr = (unsigned long)addr;
    sqe->len = len;
}

static inline void io_uring_prep_nop(struct io_uring_sqe *sqe)
{
    memset(sqe, 0, sizeof(*sqe));
    sqe->opcode = IORING_OP_NOP;
}

static inline void io_uring_prep_accept(struct io_uring_sqe *sqe, int fd,
                                         struct sockaddr *addr,
                                         socklen_t *addrlen, int flags)
{
    io_uring_prep_rw(IORING_OP_ACCEPT, sqe, fd, addr, 0,
                     (uint64_t)(unsigned long)addrlen);
    sqe->accept_flags = (uint32_t)flags;
}

static inline void io_uring_prep_connect(struct io_uring_sqe *sqe, int fd,
                                          const struct sockaddr *addr,
                                          socklen_t addrlen)
{
    io_uring_prep_rw(IORING_OP_CONNECT, sqe, fd, addr, 0, addrlen);
}

static inline void io_uring_prep_recv(struct io_uring_sqe *sqe, int sockfd,
                                       void *buf, size_t len, int flags)
{
    io_uring_prep_rw(IORING_OP_RECV, sqe, sockfd, buf, (unsigned)len, 0);
    sqe->msg_flags = (uint32_t)flags;
}

static inline void io_uring_prep_send(struct io_uring_sqe *sqe, int sockfd,
                                       const void *buf, size_t len, int flags)
{
    io_uring_prep_rw(IORING_OP_SEND, sqe, sockfd, buf, (unsigned)len, 0);
    sqe->msg_flags = (uint32_t)flags;
}

static inline void io_uring_prep_read(struct io_uring_sqe *sqe, int fd,
                                       void *buf, unsigned nbytes, __u64 offset)
{
    io_uring_prep_rw(IORING_OP_READ, sqe, fd, buf, nbytes, offset);
}

static inline void io_uring_prep_write(struct io_uring_sqe *sqe, int fd,
                                        const void *buf, unsigned nbytes,
                                        __u64 offset)
{
    io_uring_prep_rw(IORING_OP_WRITE, sqe, fd, buf, nbytes, offset);
}

static inline void io_uring_prep_openat(struct io_uring_sqe *sqe, int dfd,
                                         const char *path, int flags,
                                         mode_t mode)
{
    io_uring_prep_rw(IORING_OP_OPENAT, sqe, dfd, path, mode, 0);
    sqe->open_flags = (uint32_t)flags;
}

static inline void io_uring_prep_close(struct io_uring_sqe *sqe, int fd)
{
    io_uring_prep_rw(IORING_OP_CLOSE, sqe, fd, NULL, 0, 0);
}

static inline void io_uring_prep_fsync(struct io_uring_sqe *sqe, int fd,
                                        unsigned fsync_flags)
{
    io_uring_prep_rw(IORING_OP_FSYNC, sqe, fd, NULL, 0, 0);
    sqe->fsync_flags = fsync_flags;
}

static inline void io_uring_prep_timeout(struct io_uring_sqe *sqe,
                                          struct __kernel_timespec *ts,
                                          unsigned count, unsigned flags)
{
    io_uring_prep_rw(IORING_OP_TIMEOUT, sqe, -1, ts, 1, count);
    sqe->timeout_flags = flags;
}

static inline void io_uring_prep_cancel64(struct io_uring_sqe *sqe,
                                           __u64 user_data, int flags)
{
    io_uring_prep_rw(IORING_OP_ASYNC_CANCEL, sqe, -1, NULL, 0, 0);
    sqe->addr = user_data;
    sqe->cancel_flags = (__u32)flags;
}

static inline void io_uring_prep_splice(struct io_uring_sqe *sqe,
                                         int fd_in, int64_t off_in,
                                         int fd_out, int64_t off_out,
                                         unsigned int nbytes,
                                         unsigned int splice_flags)
{
    io_uring_prep_rw(IORING_OP_SPLICE, sqe, fd_out, NULL, nbytes,
                     (__u64)off_out);
    sqe->splice_off_in = (__u64)off_in;
    sqe->splice_fd_in = fd_in;
    sqe->splice_flags = splice_flags;
}

/*
 * Submit/complete
 */
int io_uring_submit(struct io_uring *ring);
int io_uring_submit_and_wait(struct io_uring *ring, unsigned wait_nr);

/*
 * CQE access
 */
int io_uring_wait_cqe(struct io_uring *ring, struct io_uring_cqe **cqe_ptr);
int io_uring_wait_cqe_timeout(struct io_uring *ring,
                               struct io_uring_cqe **cqe_ptr,
                               struct __kernel_timespec *ts);
int io_uring_peek_cqe(struct io_uring *ring, struct io_uring_cqe **cqe_ptr);

static inline void io_uring_cqe_seen(struct io_uring *ring,
                                      struct io_uring_cqe *cqe)
{
    if (cqe)
        io_uring_smp_store_release(ring->cq.khead, *ring->cq.khead + 1);
}

static inline __u64 io_uring_cqe_get_data64(const struct io_uring_cqe *cqe)
{
    return cqe->user_data;
}

/*
 * Register
 */
int io_uring_register_buffers(struct io_uring *ring, const struct iovec *iovecs,
                               unsigned nr_iovecs);
int io_uring_unregister_buffers(struct io_uring *ring);
int io_uring_register_files(struct io_uring *ring, const int *files,
                             unsigned nr_files);
int io_uring_unregister_files(struct io_uring *ring);

#ifdef __cplusplus
}
#endif

#endif /* LIBURING_H */
