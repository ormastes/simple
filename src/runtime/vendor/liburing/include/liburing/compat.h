/* SPDX-License-Identifier: MIT */
/*
 * Compatibility helpers for liburing.
 * Vendored minimal subset for Simple's async I/O driver.
 */

#ifndef LIBURING_COMPAT_H
#define LIBURING_COMPAT_H

#include <linux/types.h>
#include <linux/time_types.h>

/* __kernel_rwf_t may not be defined on older kernels */
#ifndef __kernel_rwf_t
typedef int __kernel_rwf_t;
#endif

#endif /* LIBURING_COMPAT_H */
