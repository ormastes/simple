// warp_shuffle.cu - Warp shuffle intrinsics demonstrations

#ifndef WARP_SHUFFLE_CU
#define WARP_SHUFFLE_CU

#include <cuda_runtime.h>

// Warp-level reduction using shuffle down
__device__ int warp_reduce_sum(int val) {
    for (int offset = 16; offset > 0; offset /= 2) {
        val += __shfl_down_sync(0xffffffff, val, offset);
    }
    return val;
}

// Warp-level prefix sum using shuffle
__device__ int warp_prefix_sum(int val) {
    int lane_id = threadIdx.x % 32;

    for (int offset = 1; offset < 32; offset *= 2) {
        int n = __shfl_up_sync(0xffffffff, val, offset);
        if (lane_id >= offset) {
            val += n;
        }
    }
    return val;
}

// Warp-level broadcast
__device__ int warp_broadcast(int val, int src_lane) {
    return __shfl_sync(0xffffffff, val, src_lane);
}

// Butterfly exchange for FFT-like patterns
__device__ int warp_butterfly(int val, int mask) {
    return __shfl_xor_sync(0xffffffff, val, mask);
}

// Block reduction using warp shuffles
__global__ void block_reduce_kernel(int* output, const int* input, int n) {
    extern __shared__ int shmem[];

    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int val = (idx < n) ? input[idx] : 0;

    // Warp-level reduction
    val = warp_reduce_sum(val);

    // First thread in each warp writes to shared memory
    int lane = threadIdx.x % 32;
    int warp_id = threadIdx.x / 32;

    if (lane == 0) {
        shmem[warp_id] = val;
    }
    __syncthreads();

    // First warp reduces the partial sums
    if (warp_id == 0) {
        val = (threadIdx.x < (blockDim.x / 32)) ? shmem[lane] : 0;
        val = warp_reduce_sum(val);

        if (threadIdx.x == 0) {
            atomicAdd(output, val);
        }
    }
}

// Warp-level scan (prefix sum)
__global__ void warp_scan_kernel(int* output, const int* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        int val = input[idx];
        int scanned = warp_prefix_sum(val);
        output[idx] = scanned;
    }
}

// Shuffle-based array reversal within warp
__global__ void warp_reverse_kernel(int* data, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        int lane_id = threadIdx.x % 32;
        int val = data[idx];

        // Reverse within warp
        int reversed = __shfl_sync(0xffffffff, val, 31 - lane_id);
        data[idx] = reversed;
    }
}

// Butterfly pattern for data exchange
__global__ void butterfly_exchange_kernel(float* data, int n, int stage) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        float val = data[idx];
        int mask = 1 << stage;

        float exchanged = __shfl_xor_sync(0xffffffff, val, mask);

        // Simple butterfly operation: add or subtract based on position
        int lane_id = threadIdx.x % 32;
        if (lane_id & mask) {
            data[idx] = val - exchanged;
        } else {
            data[idx] = val + exchanged;
        }
    }
}

#endif // WARP_SHUFFLE_CU
