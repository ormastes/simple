/**
 * @file benchmark_mode4_dbc_shadow_gpu.cu
 * @brief Mode 4: GPU command path (DBC daemon), single GPU-looped kernel.
 */

#include "benchmark_shared_sum_gpu.cuh"

int main() {
    ModeDefinition mode{
        .mode_id = 4,
        .name = "Mode 4 - GPU command + DBC daemon (GPU looped sum)",
        .pinned_host = true,
        .gpu_buffer = true,
        .gpu_command = true,
        .dbc_daemon = true,
        .gpu_cq = false,  // CQ stays host in this mode
        .gpu_sq = false,  // SQ stays host in this mode
    };

    return run_gpu_loop_benchmark(mode);
}
