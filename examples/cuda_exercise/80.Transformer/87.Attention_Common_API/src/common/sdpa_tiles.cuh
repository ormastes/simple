/**
 * @file sdpa_tiles.cuh
 * @brief Tile shapes and MMA layout constants for scaled dot-product attention
 */
#pragma once
#include <cuda_runtime.h>

namespace transformer {

/// SDPA tile configuration for shared memory blocking
struct SDPATileConfig {
    int Br;   ///< Tile rows for Q (query block size)
    int Bc;   ///< Tile cols for K (key block size)
    int D;    ///< Head dimension
};

/// Default tile configurations for different architectures
__host__ __device__ constexpr SDPATileConfig sdpa_tile_sm75() { return {64, 64, 64}; }
__host__ __device__ constexpr SDPATileConfig sdpa_tile_sm80() { return {128, 64, 64}; }
__host__ __device__ constexpr SDPATileConfig sdpa_tile_sm86() { return {128, 128, 64}; }

/// Calculate shared memory requirement for a tile config
__host__ __device__ constexpr int sdpa_smem_size(SDPATileConfig cfg) {
    return (cfg.Br * cfg.D + cfg.Bc * cfg.D) * sizeof(float);
}

} // namespace transformer
