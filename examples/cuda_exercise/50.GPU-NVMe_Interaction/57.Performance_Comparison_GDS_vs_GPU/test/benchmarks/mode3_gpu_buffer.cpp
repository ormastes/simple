/**
 * @file benchmark_mode3_host_daemon.cpp
 * @brief Mode 3: Host command + DBC daemon, GPU buffer target.
 */

#include "benchmark_shared_sum.h"

int main() {
    ModeDefinition mode{
        .mode_id = 3,
        .name = "Mode 3 - host command + DBC daemon (GPU buffer target)",
        .pinned_host = true,
        .gpu_buffer = true,
        .gpu_command = false,
        .dbc_daemon = true,
        .gpu_cq = false,
        .gpu_sq = false,
    };

    return run_host_read_sum_benchmark(mode);
}
