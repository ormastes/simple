// warp_vote.cu - Warp voting intrinsics

#ifndef WARP_VOTE_CU
#define WARP_VOTE_CU

#include <cuda_runtime.h>

// Check if all threads in warp satisfy condition
__global__ void warp_all_kernel(int* output, const int* input, int n, int threshold) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        int val = input[idx];
        bool condition = (val >= threshold);

        // Check if ALL threads in warp meet condition
        bool all_meet = __all_sync(0xffffffff, condition);

        output[idx] = all_meet ? 1 : 0;
    }
}

// Check if any thread in warp satisfies condition
__global__ void warp_any_kernel(int* output, const int* input, int n, int threshold) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        int val = input[idx];
        bool condition = (val >= threshold);

        // Check if ANY thread in warp meets condition
        bool any_meet = __any_sync(0xffffffff, condition);

        output[idx] = any_meet ? 1 : 0;
    }
}

// Count how many threads in warp satisfy condition
__global__ void warp_ballot_kernel(unsigned int* output, const int* input, int n, int threshold) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        int val = input[idx];
        bool condition = (val >= threshold);

        // Get ballot - bitmask of which threads meet condition
        unsigned int ballot = __ballot_sync(0xffffffff, condition);

        // Count set bits to get number of threads meeting condition
        unsigned int count = __popc(ballot);

        output[idx] = count;
    }
}

// Warp-level matching: find threads with same value
__global__ void warp_match_kernel(unsigned long long* output, const int* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        int val = input[idx];

        // Find all threads in warp with same value
        unsigned int match_mask = __match_any_sync(0xffffffff, val);

        output[idx] = match_mask;
    }
}

// Compact non-zero values using ballot
__global__ void warp_compact_kernel(int* output, int* output_count,
                                     const int* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        int val = input[idx];
        bool is_nonzero = (val != 0);

        // Get ballot of non-zero values
        unsigned int ballot = __ballot_sync(0xffffffff, is_nonzero);

        if (is_nonzero) {
            int lane_id = threadIdx.x % 32;

            // Count how many non-zeros before this thread
            unsigned int mask = (1u << lane_id) - 1;
            int offset = __popc(ballot & mask);

            // Compute global position
            int warp_id = idx / 32;
            int base_offset = warp_id * 32;

            output[base_offset + offset] = val;
        }

        // First thread in each warp stores count
        if ((threadIdx.x % 32) == 0) {
            atomicAdd(output_count, __popc(ballot));
        }
    }
}

#endif // WARP_VOTE_CU
