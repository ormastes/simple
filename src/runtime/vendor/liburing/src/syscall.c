/* SPDX-License-Identifier: MIT */
/*
 * io_uring syscall wrappers
 * Vendored minimal subset for Simple's async I/O driver.
 */

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <sys/syscall.h>
#include <sys/uio.h>
#include <signal.h>
#include <unistd.h>
#include <errno.h>

#include "syscall.h"
#include <liburing/compat.h>
#include <liburing/io_uring.h>

#ifdef __NR_io_uring_setup

int __sys_io_uring_setup(unsigned entries, struct io_uring_params *p)
{
    return (int)syscall(__NR_io_uring_setup, entries, p);
}

int __sys_io_uring_enter(int fd, unsigned to_submit, unsigned min_complete,
                          unsigned flags, sigset_t *sig)
{
    return (int)syscall(__NR_io_uring_enter, fd, to_submit, min_complete,
                        flags, sig, _NSIG / 8);
}

int __sys_io_uring_enter2(int fd, unsigned to_submit, unsigned min_complete,
                           unsigned flags, sigset_t *sig, size_t sz)
{
    return (int)syscall(__NR_io_uring_enter, fd, to_submit, min_complete,
                        flags, sig, sz);
}

int __sys_io_uring_register(int fd, unsigned opcode, const void *arg,
                             unsigned nr_args)
{
    return (int)syscall(__NR_io_uring_register, fd, opcode, arg, nr_args);
}

#else /* !__NR_io_uring_setup */

/* Kernel too old — stubs that return -ENOSYS */

int __sys_io_uring_setup(unsigned entries, struct io_uring_params *p)
{
    (void)entries; (void)p;
    errno = ENOSYS;
    return -1;
}

int __sys_io_uring_enter(int fd, unsigned to_submit, unsigned min_complete,
                          unsigned flags, sigset_t *sig)
{
    (void)fd; (void)to_submit; (void)min_complete; (void)flags; (void)sig;
    errno = ENOSYS;
    return -1;
}

int __sys_io_uring_enter2(int fd, unsigned to_submit, unsigned min_complete,
                           unsigned flags, sigset_t *sig, size_t sz)
{
    (void)fd; (void)to_submit; (void)min_complete; (void)flags; (void)sig; (void)sz;
    errno = ENOSYS;
    return -1;
}

int __sys_io_uring_register(int fd, unsigned opcode, const void *arg,
                             unsigned nr_args)
{
    (void)fd; (void)opcode; (void)arg; (void)nr_args;
    errno = ENOSYS;
    return -1;
}

#endif /* __NR_io_uring_setup */
