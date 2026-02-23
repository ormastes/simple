/* SPDX-License-Identifier: MIT */
/*
 * Memory barrier helpers for liburing.
 * Vendored minimal subset for Simple's async I/O driver.
 */

#ifndef LIBURING_BARRIER_H
#define LIBURING_BARRIER_H

#include <stdatomic.h>

#define io_uring_smp_store_release(p, v)                \
    atomic_store_explicit((_Atomic __typeof__(*(p)) *)(p), (v), \
                          memory_order_release)

#define io_uring_smp_load_acquire(p)                    \
    atomic_load_explicit((_Atomic __typeof__(*(p)) *)(p), \
                         memory_order_acquire)

#define io_uring_smp_mb()   atomic_thread_fence(memory_order_seq_cst)

#endif /* LIBURING_BARRIER_H */
