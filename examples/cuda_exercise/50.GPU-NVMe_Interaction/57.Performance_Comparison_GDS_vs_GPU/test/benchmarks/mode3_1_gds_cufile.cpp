/**
 * @file mode3_gds_cufile.cpp
 * @brief Mode 3-1: Host command + cuFile/GDS path (GPU buffer via GDS).
 */

#include "benchmark_shared_sum.h"

int main() {
    ModeDefinition mode{
        .mode_id = 31,  // optional Mode 3.1 (GDS/cuFile)
        .name = "Mode 3.1 - Host command + GDS/cuFile (GPU buffer, optional)",
        .pinned_host = true,
        .gpu_buffer = true,
        .gpu_command = false,
        .dbc_daemon = false,
        .gpu_cq = false,
        .gpu_sq = false,
    };

    // Note: Optional path. Reuses host-loop helper; a real GDS/cuFile setup
    // would replace the host→GPU copy with cuFile reads into GPU memory.
    return run_host_read_sum_benchmark(mode);
}
