/**
 * @file sampling.cu
 * @brief GPU-accelerated sampling strategies for text generation
 *
 * Implements top-k and top-p (nucleus) sampling on GPU using a single-block
 * approach with shared memory. These are reference implementations prioritizing
 * correctness over maximum throughput.
 */

#include "common/text_generator.h"
#include "cuda_utils.h"
#include <curand_kernel.h>

namespace llm {

// ============================================================================
// Sampling Kernels
// ============================================================================

/**
 * @brief Softmax over an array in shared memory (single-block, in-place)
 *
 * @param data    Shared memory array
 * @param n       Number of elements
 * @param tid     Thread ID within block
 * @param threads Block size
 */
__device__ void shared_softmax(float* data, int n, int tid, int threads) {
    // Find max for numerical stability
    float local_max = -1e30f;
    for (int i = tid; i < n; i += threads) {
        local_max = fmaxf(local_max, data[i]);
    }

    // Block-wide max reduction via shared memory
    __shared__ float s_max[32];
    int warp_id = tid / 32;
    int lane_id = tid % 32;

    // Warp reduction
    for (int offset = 16; offset > 0; offset >>= 1) {
        local_max = fmaxf(local_max, __shfl_down_sync(0xFFFFFFFF, local_max, offset));
    }
    if (lane_id == 0 && warp_id < 32) {
        s_max[warp_id] = local_max;
    }
    __syncthreads();

    if (tid == 0) {
        float global_max = s_max[0];
        for (int i = 1; i < (threads + 31) / 32 && i < 32; ++i) {
            global_max = fmaxf(global_max, s_max[i]);
        }
        s_max[0] = global_max;
    }
    __syncthreads();
    float max_val = s_max[0];

    // Compute exp(x - max) and sum
    float local_sum = 0.0f;
    for (int i = tid; i < n; i += threads) {
        data[i] = expf(data[i] - max_val);
        local_sum += data[i];
    }

    // Block-wide sum reduction
    __shared__ float s_sum[32];
    for (int offset = 16; offset > 0; offset >>= 1) {
        local_sum += __shfl_down_sync(0xFFFFFFFF, local_sum, offset);
    }
    if (lane_id == 0 && warp_id < 32) {
        s_sum[warp_id] = local_sum;
    }
    __syncthreads();

    if (tid == 0) {
        float global_sum = s_sum[0];
        for (int i = 1; i < (threads + 31) / 32 && i < 32; ++i) {
            global_sum += s_sum[i];
        }
        s_sum[0] = global_sum;
    }
    __syncthreads();
    float sum_val = s_sum[0];

    // Normalize
    for (int i = tid; i < n; i += threads) {
        data[i] /= sum_val;
    }
    __syncthreads();
}

/**
 * @brief Simple insertion sort in shared memory (single thread)
 *
 * Sorts indices by their values in descending order. Only called by thread 0.
 * Suitable for small arrays only (top-k candidates).
 *
 * @param values   Array of values
 * @param indices  Array of indices to sort
 * @param n        Number of elements
 */
__device__ void insertion_sort_desc(float* values, int* indices, int n) {
    for (int i = 1; i < n; ++i) {
        float key_val = values[i];
        int key_idx = indices[i];
        int j = i - 1;
        while (j >= 0 && values[j] < key_val) {
            values[j + 1] = values[j];
            indices[j + 1] = indices[j];
            --j;
        }
        values[j + 1] = key_val;
        indices[j + 1] = key_idx;
    }
}

/**
 * @brief Top-k sampling kernel
 *
 * Each block processes one sampling request. Thread 0 performs the sorting
 * and sampling after all threads cooperatively find the top-k candidates.
 * For small vocab sizes, thread 0 does all the work.
 */
__global__ void top_k_sampling_kernel(
    int* output_token, const float* logits, int vocab_size,
    int top_k, float temperature, unsigned long long seed
) {
    extern __shared__ float shared_mem[];
    float* s_logits = shared_mem;
    int* s_indices = (int*)(shared_mem + vocab_size);

    int tid = threadIdx.x;
    int threads = blockDim.x;

    // Copy logits to shared memory and apply temperature
    for (int i = tid; i < vocab_size; i += threads) {
        s_logits[i] = logits[i] / temperature;
        s_indices[i] = i;
    }
    __syncthreads();

    // Thread 0 performs the top-k selection and sampling
    if (tid == 0) {
        // Clamp top_k
        int k = min(top_k, vocab_size);

        // Partial sort: find top-k elements using selection
        for (int i = 0; i < k; ++i) {
            int max_idx = i;
            float max_val = s_logits[i];
            for (int j = i + 1; j < vocab_size; ++j) {
                if (s_logits[j] > max_val) {
                    max_val = s_logits[j];
                    max_idx = j;
                }
            }
            // Swap
            if (max_idx != i) {
                float tmp_val = s_logits[i];
                s_logits[i] = s_logits[max_idx];
                s_logits[max_idx] = tmp_val;

                int tmp_idx = s_indices[i];
                s_indices[i] = s_indices[max_idx];
                s_indices[max_idx] = tmp_idx;
            }
        }

        // Softmax over top-k logits
        float max_logit = s_logits[0];
        float sum = 0.0f;
        for (int i = 0; i < k; ++i) {
            s_logits[i] = expf(s_logits[i] - max_logit);
            sum += s_logits[i];
        }
        for (int i = 0; i < k; ++i) {
            s_logits[i] /= sum;
        }

        // Sample from the distribution using curand
        curandState state;
        curand_init(seed, 0, 0, &state);
        float r = curand_uniform(&state);

        // Find the sampled token
        float cumsum = 0.0f;
        int sampled = s_indices[k - 1];  // Default to last
        for (int i = 0; i < k; ++i) {
            cumsum += s_logits[i];
            if (r <= cumsum) {
                sampled = s_indices[i];
                break;
            }
        }

        *output_token = sampled;
    }
}

/**
 * @brief Top-p (nucleus) sampling kernel
 *
 * Sorts logits by probability, accumulates until cumulative probability
 * exceeds top_p, then samples from the nucleus set.
 */
__global__ void top_p_sampling_kernel(
    int* output_token, const float* logits, int vocab_size,
    float top_p, float temperature, unsigned long long seed
) {
    extern __shared__ float shared_mem[];
    float* s_logits = shared_mem;
    int* s_indices = (int*)(shared_mem + vocab_size);

    int tid = threadIdx.x;
    int threads = blockDim.x;

    // Copy logits to shared memory and apply temperature
    for (int i = tid; i < vocab_size; i += threads) {
        s_logits[i] = logits[i] / temperature;
        s_indices[i] = i;
    }
    __syncthreads();

    // Thread 0 performs sorting and sampling
    if (tid == 0) {
        // Softmax to get probabilities
        float max_logit = s_logits[0];
        for (int i = 1; i < vocab_size; ++i) {
            max_logit = fmaxf(max_logit, s_logits[i]);
        }
        float sum = 0.0f;
        for (int i = 0; i < vocab_size; ++i) {
            s_logits[i] = expf(s_logits[i] - max_logit);
            sum += s_logits[i];
        }
        for (int i = 0; i < vocab_size; ++i) {
            s_logits[i] /= sum;
        }

        // Sort by probability (descending) - selection sort for correctness
        for (int i = 0; i < vocab_size - 1; ++i) {
            int max_idx = i;
            float max_val = s_logits[i];
            for (int j = i + 1; j < vocab_size; ++j) {
                if (s_logits[j] > max_val) {
                    max_val = s_logits[j];
                    max_idx = j;
                }
            }
            if (max_idx != i) {
                float tmp_val = s_logits[i];
                s_logits[i] = s_logits[max_idx];
                s_logits[max_idx] = tmp_val;

                int tmp_idx = s_indices[i];
                s_indices[i] = s_indices[max_idx];
                s_indices[max_idx] = tmp_idx;
            }

            // Early exit: if cumulative prob already exceeds top_p, stop sorting
            float cumsum = 0.0f;
            for (int k = 0; k <= i; ++k) {
                cumsum += s_logits[k];
            }
            if (cumsum >= top_p) {
                // Only need to consider indices [0, i]
                break;
            }
        }

        // Find nucleus: smallest set whose cumulative probability >= top_p
        float cumsum = 0.0f;
        int nucleus_size = vocab_size;
        for (int i = 0; i < vocab_size; ++i) {
            cumsum += s_logits[i];
            if (cumsum >= top_p) {
                nucleus_size = i + 1;
                break;
            }
        }

        // Re-normalize probabilities within the nucleus
        float nucleus_sum = 0.0f;
        for (int i = 0; i < nucleus_size; ++i) {
            nucleus_sum += s_logits[i];
        }
        for (int i = 0; i < nucleus_size; ++i) {
            s_logits[i] /= nucleus_sum;
        }

        // Sample from nucleus
        curandState state;
        curand_init(seed, 0, 0, &state);
        float r = curand_uniform(&state);

        cumsum = 0.0f;
        int sampled = s_indices[nucleus_size - 1];  // Default to last in nucleus
        for (int i = 0; i < nucleus_size; ++i) {
            cumsum += s_logits[i];
            if (r <= cumsum) {
                sampled = s_indices[i];
                break;
            }
        }

        *output_token = sampled;
    }
}

// ============================================================================
// Host API implementations
// ============================================================================

void gpu_top_k_sampling(int* output_token, const float* logits, int vocab_size,
                       int top_k, float temperature, cudaStream_t stream) {
    // Shared memory: vocab_size floats + vocab_size ints
    size_t shared_size = vocab_size * (sizeof(float) + sizeof(int));

    // Use a simple seed based on clock
    unsigned long long seed;
    CHECK_CUDA(cudaMemcpyAsync(&seed, output_token, sizeof(int),
                                cudaMemcpyDeviceToHost, stream));
    CHECK_CUDA(cudaStreamSynchronize(stream));
    seed = (unsigned long long)clock() ^ ((unsigned long long)seed << 16);

    int threads = min(256, vocab_size);
    top_k_sampling_kernel<<<1, threads, shared_size, stream>>>(
        output_token, logits, vocab_size, top_k, temperature, seed);
    CHECK_LAST_CUDA_ERROR();
}

void gpu_top_p_sampling(int* output_token, const float* logits, int vocab_size,
                       float top_p, float temperature, cudaStream_t stream) {
    // Shared memory: vocab_size floats + vocab_size ints
    size_t shared_size = vocab_size * (sizeof(float) + sizeof(int));

    // Use a simple seed based on clock
    unsigned long long seed;
    CHECK_CUDA(cudaMemcpyAsync(&seed, output_token, sizeof(int),
                                cudaMemcpyDeviceToHost, stream));
    CHECK_CUDA(cudaStreamSynchronize(stream));
    seed = (unsigned long long)clock() ^ ((unsigned long long)seed << 16);

    int threads = min(256, vocab_size);
    top_p_sampling_kernel<<<1, threads, shared_size, stream>>>(
        output_token, logits, vocab_size, top_p, temperature, seed);
    CHECK_LAST_CUDA_ERROR();
}

} // namespace llm
