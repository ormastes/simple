/**
 * @file adamw_optimizer.cpp
 * @brief Host-side AdamW optimizer state management
 *
 * Provides allocation and deallocation of AdamW optimizer state buffers
 * (first and second moment estimates) on GPU device memory. The actual
 * parameter update is performed by the GPU kernel in adamw_kernel.cu.
 */

#include "common/optimizer.h"
#include <cuda_runtime.h>
#include <cstring>

namespace llm {

/**
 * @brief Allocate AdamW optimizer state on GPU
 *
 * Allocates device memory for first moment (m) and second moment (v)
 * buffers, both initialized to zero. The step counter starts at zero.
 *
 * @param num_params Number of parameters to track
 * @return AdamWState with zero-initialized moment buffers on device
 *
 * @note Caller is responsible for calling free_adamw_state() when done
 */
AdamWState allocate_adamw_state(size_t num_params) {
    AdamWState state;
    state.size = num_params;
    state.step = 0;
    state.d_m = nullptr;
    state.d_v = nullptr;

    size_t bytes = num_params * sizeof(float);

    // Allocate first moment buffer (m) and initialize to zero
    cudaMalloc(&state.d_m, bytes);
    cudaMemset(state.d_m, 0, bytes);

    // Allocate second moment buffer (v) and initialize to zero
    cudaMalloc(&state.d_v, bytes);
    cudaMemset(state.d_v, 0, bytes);

    return state;
}

/**
 * @brief Free AdamW optimizer state
 *
 * Releases all device memory associated with the optimizer state
 * and resets pointers to nullptr for safety.
 *
 * @param[in,out] state State to free; all device pointers freed and nulled
 */
void free_adamw_state(AdamWState& state) {
    if (state.d_m) {
        cudaFree(state.d_m);
        state.d_m = nullptr;
    }
    if (state.d_v) {
        cudaFree(state.d_v);
        state.d_v = nullptr;
    }
    state.step = 0;
    state.size = 0;
}

} // namespace llm
