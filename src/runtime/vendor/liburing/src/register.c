/* SPDX-License-Identifier: MIT */
/*
 * io_uring register operations
 * Vendored minimal subset for Simple's async I/O driver.
 */

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <sys/uio.h>
#include <errno.h>

#include <liburing.h>
#include "syscall.h"

/* Register operation codes */
#define IORING_REGISTER_BUFFERS     0
#define IORING_UNREGISTER_BUFFERS   1
#define IORING_REGISTER_FILES       2
#define IORING_UNREGISTER_FILES     3

int io_uring_register_buffers(struct io_uring *ring, const struct iovec *iovecs,
                               unsigned nr_iovecs)
{
    int ret = __sys_io_uring_register(ring->ring_fd, IORING_REGISTER_BUFFERS,
                                      iovecs, nr_iovecs);
    if (ret < 0)
        return -errno;
    return ret;
}

int io_uring_unregister_buffers(struct io_uring *ring)
{
    int ret = __sys_io_uring_register(ring->ring_fd, IORING_UNREGISTER_BUFFERS,
                                      NULL, 0);
    if (ret < 0)
        return -errno;
    return ret;
}

int io_uring_register_files(struct io_uring *ring, const int *files,
                             unsigned nr_files)
{
    int ret = __sys_io_uring_register(ring->ring_fd, IORING_REGISTER_FILES,
                                      files, nr_files);
    if (ret < 0)
        return -errno;
    return ret;
}

int io_uring_unregister_files(struct io_uring *ring)
{
    int ret = __sys_io_uring_register(ring->ring_fd, IORING_UNREGISTER_FILES,
                                      NULL, 0);
    if (ret < 0)
        return -errno;
    return ret;
}
