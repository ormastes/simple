#ifndef SIMPLE_RUNTIME_DISK_HEADROOM_PRIVATE_H
#define SIMPLE_RUNTIME_DISK_HEADROOM_PRIVATE_H
#include <stdint.h>
#include <limits.h>
/* statvfs units multiply before crossing the signed runtime ABI. */
static inline int64_t rt_disk_headroom_product_v1(uint64_t blocks, uint64_t unit) {
    if (unit != 0 && blocks > (uint64_t)INT64_MAX / unit) return INT64_MAX;
    return (int64_t)(blocks * unit);
}
#endif
