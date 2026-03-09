/**
 * @file kv_cache_ops.h
 * @brief Host-side wrapper declarations for KV-cache CUDA kernels
 */

#pragma once

#include "inference_engine.h"

namespace llm {

void kv_cache_append(KVCache& cache, const float* new_keys, const float* new_values,
                     int layer_idx, int num_new, cudaStream_t stream = 0);

void kv_cache_rotate(KVCache& cache, int layer_idx, int shift, cudaStream_t stream = 0);

} // namespace llm
