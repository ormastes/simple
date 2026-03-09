/**
 * @file autotune_registry.cuh
 * @brief Shape-to-kernel cache interface for GEMM autotuning
 */
#pragma once
#include <cuda_runtime.h>

namespace transformer {

/**
 * @brief GEMM kernel variant
 */
enum class GemmKernel {
    SIMT_FP32,    ///< SIMT shared-memory GEMM (fp32)
    WMMA_FP16,    ///< Tensor Core WMMA GEMM (fp16)
    INT8_DP4A     ///< INT8 DP4A GEMM
};

/**
 * @brief GEMM configuration key for autotuning cache
 */
struct GemmConfig {
    int M, N, K;
    GemmKernel kernel;
    int tile_m, tile_n, tile_k;  ///< Tile dimensions
    int sm_version;              ///< SM architecture version
};

/**
 * @brief Look up best known config for given problem size
 * @param[in] M Rows of A
 * @param[in] N Cols of B
 * @param[in] K Inner dimension
 * @param[in] sm SM version (e.g., 75 for Turing)
 * @return Best GemmConfig, or default if not cached
 */
GemmConfig get_best_config(int M, int N, int K, int sm);

/**
 * @brief Register a config as best for given problem size
 */
void register_config(const GemmConfig& config);

/**
 * @brief Clear the autotuning cache
 */
void clear_autotune_cache();

} // namespace transformer
