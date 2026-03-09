/**
 * @file benchmark_mode0_baseline.cpp
 * @brief Mode 0: Host commands, pageable host buffer, host CQ/SQ.
 */

#include "benchmark_shared_sum.h"

int main() {
    ModeDefinition mode{
        .mode_id = 0,
        .name = "Mode 0 - host command, pageable host buffer",
        .pinned_host = false,
        .gpu_buffer = false,
        .gpu_command = false,
        .dbc_daemon = false,
        .gpu_cq = false,
        .gpu_sq = false,
    };

    return run_host_read_sum_benchmark(mode);
}
