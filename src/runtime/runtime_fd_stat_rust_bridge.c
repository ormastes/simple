/* Private C implementation for the Rust runtime's public fd-stat ABI alias.
 * The native C product exports the same behavior from runtime_native.c. */
#include "runtime_fd_stat_v1.h"

int64_t spl_c_fd_stat_snapshot_v1(int64_t descriptor, int64_t out_addr, int64_t out_bytes) {
    return rt_fd_stat_snapshot_v1_impl(
        descriptor, (uint64_t *)(uintptr_t)out_addr, out_bytes);
}
