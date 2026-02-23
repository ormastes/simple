/* SPDX-License-Identifier: MIT */
/*
 * io_uring setup/teardown implementation
 * Vendored minimal subset for Simple's async I/O driver.
 */

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <sys/mman.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>

#include <liburing.h>
#include "syscall.h"

static int io_uring_mmap(int fd, struct io_uring_params *p,
                          struct io_uring_sq *sq, struct io_uring_cq *cq)
{
    size_t size;
    int ret;

    /* Map SQ ring */
    sq->ring_sz = p->sq_off.array + p->sq_entries * sizeof(unsigned);
    sq->ring_ptr = mmap(0, sq->ring_sz, PROT_READ | PROT_WRITE,
                         MAP_SHARED | MAP_POPULATE, fd,
                         0 /* IORING_OFF_SQ_RING */);
    if (sq->ring_ptr == MAP_FAILED)
        return -errno;

    sq->khead = sq->ring_ptr + p->sq_off.head;
    sq->ktail = sq->ring_ptr + p->sq_off.tail;
    sq->kring_mask = sq->ring_ptr + p->sq_off.ring_mask;
    sq->kring_entries = sq->ring_ptr + p->sq_off.ring_entries;
    sq->kflags = sq->ring_ptr + p->sq_off.flags;
    sq->kdropped = sq->ring_ptr + p->sq_off.dropped;
    sq->array = sq->ring_ptr + p->sq_off.array;
    sq->ring_mask = *sq->kring_mask;
    sq->ring_entries = *sq->kring_entries;

    /* Map SQEs */
    size = p->sq_entries * sizeof(struct io_uring_sqe);
    sq->sqes = mmap(0, size, PROT_READ | PROT_WRITE,
                     MAP_SHARED | MAP_POPULATE, fd,
                     0x10000000ULL /* IORING_OFF_SQES */);
    if (sq->sqes == MAP_FAILED) {
        ret = -errno;
        goto err_sq;
    }

    /* Map CQ ring */
    cq->ring_sz = p->cq_off.cqes + p->cq_entries * sizeof(struct io_uring_cqe);
    cq->ring_ptr = mmap(0, cq->ring_sz, PROT_READ | PROT_WRITE,
                         MAP_SHARED | MAP_POPULATE, fd,
                         0x8000000ULL /* IORING_OFF_CQ_RING */);
    if (cq->ring_ptr == MAP_FAILED) {
        ret = -errno;
        goto err_sqes;
    }

    cq->khead = cq->ring_ptr + p->cq_off.head;
    cq->ktail = cq->ring_ptr + p->cq_off.tail;
    cq->kring_mask = cq->ring_ptr + p->cq_off.ring_mask;
    cq->kring_entries = cq->ring_ptr + p->cq_off.ring_entries;
    cq->koverflow = cq->ring_ptr + p->cq_off.overflow;
    cq->cqes = cq->ring_ptr + p->cq_off.cqes;
    cq->ring_mask = *cq->kring_mask;
    cq->ring_entries = *cq->kring_entries;

    return 0;

err_sqes:
    munmap(sq->sqes, p->sq_entries * sizeof(struct io_uring_sqe));
err_sq:
    munmap(sq->ring_ptr, sq->ring_sz);
    return ret;
}

int io_uring_queue_init_params(unsigned entries, struct io_uring *ring,
                                struct io_uring_params *p)
{
    int fd, ret;

    memset(ring, 0, sizeof(*ring));

    fd = __sys_io_uring_setup(entries, p);
    if (fd < 0)
        return -errno;

    ring->ring_fd = fd;
    ring->enter_ring_fd = fd;
    ring->flags = p->flags;
    ring->features = p->features;

    ret = io_uring_mmap(fd, p, &ring->sq, &ring->cq);
    if (ret) {
        close(fd);
        return ret;
    }

    /* Initialize SQ array indices (identity mapping) */
    unsigned *array = ring->sq.array;
    for (unsigned i = 0; i < p->sq_entries; i++)
        array[i] = i;

    ring->sq.sqe_head = 0;
    ring->sq.sqe_tail = 0;

    return 0;
}

int io_uring_queue_init(unsigned entries, struct io_uring *ring, unsigned flags)
{
    struct io_uring_params p;
    memset(&p, 0, sizeof(p));
    p.flags = flags;
    return io_uring_queue_init_params(entries, ring, &p);
}

void io_uring_queue_exit(struct io_uring *ring)
{
    struct io_uring_sq *sq = &ring->sq;
    struct io_uring_cq *cq = &ring->cq;

    if (sq->sqes)
        munmap(sq->sqes, sq->ring_entries * sizeof(struct io_uring_sqe));
    if (sq->ring_ptr)
        munmap(sq->ring_ptr, sq->ring_sz);
    if (cq->ring_ptr && cq->ring_ptr != sq->ring_ptr)
        munmap(cq->ring_ptr, cq->ring_sz);

    if (ring->ring_fd >= 0)
        close(ring->ring_fd);
}
