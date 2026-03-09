/**
 * @file benchmark_mode1_gds.cpp
 * @brief Mode 1: Host commands, pinned host buffer, host CQ/SQ.
 */

#include "benchmark_shared_sum.h"

int main() {
    ModeDefinition mode{
        .mode_id = 1,
        .name = "Mode 1 - host command, pinned host buffer",
        .pinned_host = true,
        .gpu_buffer = false,
        .gpu_command = false,
        .dbc_daemon = false,
        .gpu_cq = false,
        .gpu_sq = false,
    };

    return run_host_read_sum_benchmark(mode);
}
