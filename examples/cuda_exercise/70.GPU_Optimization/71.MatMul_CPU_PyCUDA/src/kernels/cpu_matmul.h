/**
 * @file cpu_matmul.h
 * @brief CPU matrix multiplication header
 */

#pragma once

#include <chrono>
#include <cstring>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Naive CPU matrix multiplication: C = A × B
 */
void cpu_matmul_naive(float* C, const float* A, const float* B,
                     int M, int N, int K);

/**
 * Cache-optimized tiled matrix multiplication
 */
void cpu_matmul_tiled(float* C, const float* A, const float* B,
                     int M, int N, int K, int tile_size);

/**
 * Multi-threaded parallel matrix multiplication
 */
void cpu_matmul_parallel(float* C, const float* A, const float* B,
                        int M, int N, int K, int num_threads);

/**
 * Matrix multiplication with performance timing
 */
float cpu_matmul_timed(float* C, const float* A, const float* B,
                      int M, int N, int K, const char* method);

#ifdef __cplusplus
}
#endif
