/**
 * @file benchmark_mode2_host_daemon_gpu_mem.cpp
 * @brief Mode 2: Host command + DBC daemon, pinned host buffer.
 */

#include "benchmark_shared_sum.h"

int main() {
    ModeDefinition mode{
        .mode_id = 2,
        .name = "Mode 2 - host command + DBC daemon (pinned host)",
        .pinned_host = true,
        .gpu_buffer = false,
        .gpu_command = false,
        .dbc_daemon = true,
        .gpu_cq = false,
        .gpu_sq = false,
    };

    return run_host_read_sum_benchmark(mode);
}
