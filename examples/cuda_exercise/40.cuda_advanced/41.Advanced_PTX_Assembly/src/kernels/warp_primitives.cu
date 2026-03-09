// warp_primitives.cu - Warp-level PTX operations
// Demonstrates shuffle, vote, and ballot operations using inline PTX

#ifndef WARP_PRIMITIVES_CU
#define WARP_PRIMITIVES_CU

// ============================================================================
// Warp Shuffle Operations
// ============================================================================

__device__ int shfl_down_ptx(int val, unsigned int delta) {
    int result;
    // Shuffle down: get value from lane (threadIdx.x + delta)
    asm("shfl.sync.down.b32 %0, %1, %2, 0x1f, 0xffffffff;"
        : "=r"(result)
        : "r"(val), "r"(delta)
    );
    return result;
}

__device__ int shfl_up_ptx(int val, unsigned int delta) {
    int result;
    // Shuffle up: get value from lane (threadIdx.x - delta)
    asm("shfl.sync.up.b32 %0, %1, %2, 0x0, 0xffffffff;"
        : "=r"(result)
        : "r"(val), "r"(delta)
    );
    return result;
}

__device__ int shfl_xor_ptx(int val, unsigned int mask) {
    int result;
    // Shuffle XOR: get value from lane (threadIdx.x ^ mask)
    asm("shfl.sync.bfly.b32 %0, %1, %2, 0x1f, 0xffffffff;"
        : "=r"(result)
        : "r"(val), "r"(mask)
    );
    return result;
}

__device__ int shfl_idx_ptx(int val, unsigned int src_lane) {
    int result;
    // Shuffle index: get value from specific lane
    asm("shfl.sync.idx.b32 %0, %1, %2, 0x1f, 0xffffffff;"
        : "=r"(result)
        : "r"(val), "r"(src_lane)
    );
    return result;
}

// ============================================================================
// Warp Vote Operations
// ============================================================================

__device__ bool vote_all_ptx(bool predicate) {
    int result;
    int pred = predicate ? 1 : 0;
    // Returns 1 if all threads in warp have predicate == true
    asm("vote.sync.all.pred %0, %1, 0xffffffff;"
        : "=r"(result)
        : "r"(pred)
    );
    return result != 0;
}

__device__ bool vote_any_ptx(bool predicate) {
    int result;
    int pred = predicate ? 1 : 0;
    // Returns 1 if any thread in warp has predicate == true
    asm("vote.sync.any.pred %0, %1, 0xffffffff;"
        : "=r"(result)
        : "r"(pred)
    );
    return result != 0;
}

__device__ unsigned int ballot_ptx(bool predicate) {
    unsigned int result;
    int pred = predicate ? 1 : 0;
    // Returns bitmask where bit i is set if thread i has predicate == true
    asm("vote.sync.ballot.b32 %0, %1, 0xffffffff;"
        : "=r"(result)
        : "r"(pred)
    );
    return result;
}

// ============================================================================
// Warp Reduction Operations
// ============================================================================

__device__ int warp_reduce_sum_ptx(int val) {
    // Warp reduction using shuffle down
    #pragma unroll
    for (int offset = 16; offset > 0; offset /= 2) {
        val += shfl_down_ptx(val, offset);
    }
    return val;  // Valid in lane 0
}

__device__ int warp_reduce_max_ptx(int val) {
    // Warp reduction for maximum value
    #pragma unroll
    for (int offset = 16; offset > 0; offset /= 2) {
        int other = shfl_down_ptx(val, offset);
        val = max(val, other);
    }
    return val;  // Valid in lane 0
}

__device__ int warp_reduce_min_ptx(int val) {
    // Warp reduction for minimum value
    #pragma unroll
    for (int offset = 16; offset > 0; offset /= 2) {
        int other = shfl_down_ptx(val, offset);
        val = min(val, other);
    }
    return val;  // Valid in lane 0
}

__device__ float warp_reduce_sum_float_ptx(float val) {
    // Warp reduction for float
    #pragma unroll
    for (int offset = 16; offset > 0; offset /= 2) {
        int val_int = __float_as_int(val);
        int result_int;
        asm("shfl.sync.down.b32 %0, %1, %2, 0x1f, 0xffffffff;"
            : "=r"(result_int)
            : "r"(val_int), "r"(offset)
        );
        val += __int_as_float(result_int);
    }
    return val;
}

// ============================================================================
// Test Kernels
// ============================================================================

__global__ void init_lane_ids_kernel(int* data) {
    int lane = threadIdx.x % 32;
    data[threadIdx.x] = lane;
}

__global__ void shuffle_down_kernel(int* output, const int* input, unsigned int delta) {
    int lane = threadIdx.x % 32;
    int val = input[threadIdx.x];
    output[threadIdx.x] = shfl_down_ptx(val, delta);
}

__global__ void shuffle_up_kernel(int* output, const int* input, unsigned int delta) {
    int val = input[threadIdx.x];
    output[threadIdx.x] = shfl_up_ptx(val, delta);
}

__global__ void shuffle_xor_kernel(int* output, const int* input, unsigned int mask) {
    int val = input[threadIdx.x];
    output[threadIdx.x] = shfl_xor_ptx(val, mask);
}

__global__ void warp_reduce_sum_kernel(int* result, const int* data) {
    int lane = threadIdx.x % 32;
    int val = data[threadIdx.x];

    // Reduce within warp
    int warp_sum = warp_reduce_sum_ptx(val);

    // Lane 0 writes result
    if (lane == 0) {
        *result = warp_sum;
    }
}

__global__ void warp_reduce_max_kernel(int* result, const int* data) {
    int lane = threadIdx.x % 32;
    int val = data[threadIdx.x];

    int warp_max = warp_reduce_max_ptx(val);

    if (lane == 0) {
        *result = warp_max;
    }
}

__global__ void ballot_kernel(unsigned int* result, const int* data, int threshold) {
    int val = data[threadIdx.x];
    bool pred = (val > threshold);

    unsigned int mask = ballot_ptx(pred);

    if (threadIdx.x == 0) {
        *result = mask;
    }
}

__global__ void vote_all_kernel(int* result, const int* data, int expected_val) {
    int val = data[threadIdx.x];
    bool all_match = vote_all_ptx(val == expected_val);

    if (threadIdx.x == 0) {
        *result = all_match ? 1 : 0;
    }
}

__global__ void vote_any_kernel(int* result, const int* data, int search_val) {
    int val = data[threadIdx.x];
    bool any_match = vote_any_ptx(val == search_val);

    if (threadIdx.x == 0) {
        *result = any_match ? 1 : 0;
    }
}

// Block-wide reduction using warp primitives
__global__ void block_reduce_sum_kernel(int* result, const int* data, int n) {
    __shared__ int warp_sums[32];  // Max 32 warps per block

    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int lane = threadIdx.x % 32;
    int warp_id = threadIdx.x / 32;

    // Each thread loads its value
    int val = (idx < n) ? data[idx] : 0;

    // Reduce within warp
    int warp_sum = warp_reduce_sum_ptx(val);

    // Lane 0 of each warp writes to shared memory
    if (lane == 0) {
        warp_sums[warp_id] = warp_sum;
    }
    __syncthreads();

    // First warp reduces warp sums
    if (warp_id == 0) {
        int num_warps = (blockDim.x + 31) / 32;
        val = (lane < num_warps) ? warp_sums[lane] : 0;
        int block_sum = warp_reduce_sum_ptx(val);

        if (lane == 0) {
            atomicAdd(result, block_sum);
        }
    }
}

#endif // WARP_PRIMITIVES_CU
