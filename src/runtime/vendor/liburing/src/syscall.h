/* SPDX-License-Identifier: MIT */
/*
 * io_uring syscall wrappers
 */

#ifndef LIBURING_SYSCALL_H
#define LIBURING_SYSCALL_H

#include <signal.h>
#include <stdint.h>

struct io_uring_params;

int __sys_io_uring_setup(unsigned entries, struct io_uring_params *p);
int __sys_io_uring_enter(int fd, unsigned to_submit, unsigned min_complete,
                          unsigned flags, sigset_t *sig);
int __sys_io_uring_enter2(int fd, unsigned to_submit, unsigned min_complete,
                           unsigned flags, sigset_t *sig, size_t sz);
int __sys_io_uring_register(int fd, unsigned opcode, const void *arg,
                             unsigned nr_args);

#endif /* LIBURING_SYSCALL_H */
