/* SPDX-License-Identifier: MIT */
/*
 * io_uring submit/complete queue operations
 * Vendored minimal subset for Simple's async I/O driver.
 */

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <errno.h>
#include <poll.h>
#include <string.h>
#include <time.h>

#include <liburing.h>
#include <liburing/io_uring.h>
#include "syscall.h"

/*
 * Flush pending SQEs to the kernel SQ ring
 */
static void io_uring_flush_sq(struct io_uring *ring)
{
    struct io_uring_sq *sq = &ring->sq;
    unsigned tail = sq->sqe_tail;
    unsigned to_submit = tail - sq->sqe_head;

    if (!to_submit)
        return;

    /*
     * Fill in SQ array entries with sequential indices.
     * sqe_head..sqe_tail range has been filled by get_sqe.
     */
    unsigned mask = sq->ring_mask;
    unsigned ktail = io_uring_smp_load_acquire(sq->ktail);

    for (unsigned i = sq->sqe_head; i != tail; i++) {
        sq->array[ktail & mask] = i & mask;
        ktail++;
    }

    io_uring_smp_store_release(sq->ktail, ktail);
    sq->sqe_head = tail;

}

static unsigned io_uring_sq_ready(struct io_uring *ring)
{
    struct io_uring_sq *sq = &ring->sq;
    unsigned head = io_uring_smp_load_acquire(sq->khead);
    unsigned tail = io_uring_smp_load_acquire(sq->ktail);
    return tail - head;
}

static int io_uring_submit_ready(struct io_uring *ring)
{
    unsigned remaining = io_uring_sq_ready(ring);
    int submitted = 0;

    while (remaining) {
        int ret = __sys_io_uring_enter(ring->enter_ring_fd, remaining, 0, 0, NULL);
        if (ret < 0) {
            if (errno == EINTR)
                continue;
            return submitted ? submitted : -errno;
        }
        if (ret == 0)
            break;
        submitted += ret;
        remaining -= (unsigned)ret;
    }
    return submitted;
}

int io_uring_submit(struct io_uring *ring)
{
    io_uring_flush_sq(ring);
    return io_uring_submit_ready(ring);
}

int io_uring_submit_and_wait(struct io_uring *ring, unsigned wait_nr)
{
    io_uring_flush_sq(ring);
    int submitted = io_uring_submit_ready(ring);
    if (submitted < 0 || !wait_nr)
        return submitted;

    struct io_uring_cqe *cqe = NULL;
    int ret = io_uring_wait_cqe(ring, &cqe);
    return ret < 0 && submitted == 0 ? ret : submitted;
}

/*
 * Internal: check for available CQE
 */
static inline int __io_uring_peek_cqe(struct io_uring *ring,
                                       struct io_uring_cqe **cqe_ptr)
{
    struct io_uring_cq *cq = &ring->cq;
    unsigned head = io_uring_smp_load_acquire(cq->khead);
    unsigned tail = *cq->ktail;

    if (head != tail) {
        *cqe_ptr = &cq->cqes[head & cq->ring_mask];
        return 0;
    }

    *cqe_ptr = NULL;
    return -EAGAIN;
}

int io_uring_peek_cqe(struct io_uring *ring, struct io_uring_cqe **cqe_ptr)
{
    return __io_uring_peek_cqe(ring, cqe_ptr);
}

int io_uring_wait_cqe(struct io_uring *ring, struct io_uring_cqe **cqe_ptr)
{
    int ret;

    /* Fast path: check if a CQE is already available */
    ret = __io_uring_peek_cqe(ring, cqe_ptr);
    if (ret == 0)
        return 0;

    /* Slow path: enter kernel to wait */
    ret = __sys_io_uring_enter(ring->enter_ring_fd, 0, 1,
                                IORING_ENTER_GETEVENTS, NULL);
    if (ret < 0)
        return -errno;

    return __io_uring_peek_cqe(ring, cqe_ptr);
}

int io_uring_wait_cqe_timeout(struct io_uring *ring,
                               struct io_uring_cqe **cqe_ptr,
                               struct __kernel_timespec *ts)
{
    int ret;

    /* Fast path */
    ret = __io_uring_peek_cqe(ring, cqe_ptr);
    if (ret == 0)
        return 0;

    if (!ts) {
        /* No timeout — blocking wait */
        return io_uring_wait_cqe(ring, cqe_ptr);
    }

    if (ts->tv_sec == 0 && ts->tv_nsec == 0) {
        /* Non-blocking — already checked above */
        return -EAGAIN;
    }

    /* Polling the ring fd is the timeout-capable compatibility path for
     * kernels predating IORING_ENTER_EXT_ARG.  Never silently turn a bounded
     * wait into an unbounded enter syscall. */
    struct pollfd pfd = { .fd = ring->enter_ring_fd, .events = POLLIN };
    struct timespec timeout = {
        .tv_sec = (time_t)ts->tv_sec,
        .tv_nsec = (long)ts->tv_nsec,
    };
    ret = ppoll(&pfd, 1, &timeout, NULL);
    if (ret < 0)
        return -errno;
    if (ret == 0)
        return -ETIME;

    return __io_uring_peek_cqe(ring, cqe_ptr);
}
