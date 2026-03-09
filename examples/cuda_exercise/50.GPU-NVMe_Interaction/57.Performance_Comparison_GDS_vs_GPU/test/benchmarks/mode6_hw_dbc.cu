/**
 * @file benchmark_mode6_hardware_dbc_gpu.cu
 * @brief Mode 6: GPU command + hardware DBC (looped on GPU). Stub-friendly.
 */

#include "benchmark_shared_sum_gpu.cuh"

int main() {
    ModeDefinition mode{
        .mode_id = 6,
        .name = "Mode 6 - GPU command + hardware DBC",
        .pinned_host = true,
        .gpu_buffer = true,
        .gpu_command = true,
        .dbc_daemon = false,  // hardware DBC expected
        .gpu_cq = true,
        .gpu_sq = true,
    };

    return run_gpu_loop_benchmark(mode);
}
