/**
 * @file benchmark_mode5_dbc_daemon_gpu_command.cu
 * @brief Mode 5: GPU command + DBC daemon, GPU CQ/SQ conceptually.
 */

#include "benchmark_shared_sum_gpu.cuh"

int main() {
    ModeDefinition mode{
        .mode_id = 5,
        .name = "Mode 5 - GPU command + DBC daemon (GPU CQ target)",
        .pinned_host = true,
        .gpu_buffer = true,
        .gpu_command = true,
        .dbc_daemon = true,
        .gpu_cq = true,
        .gpu_sq = false,  // SQ stays host
    };

    return run_gpu_loop_benchmark(mode);
}
