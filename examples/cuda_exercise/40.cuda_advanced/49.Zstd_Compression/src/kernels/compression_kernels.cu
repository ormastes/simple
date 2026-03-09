// compression_kernels.cu - Simplified compression concepts on GPU
// Note: This is a simplified demonstration, not full Zstd implementation

#include <cuda_runtime.h>

// Simple run-length encoding (RLE) compression
__global__ void rle_compress(const int* input, int* output, int* lengths, int n, int* output_size) {
    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx >= n) return;

    // Each thread checks if it starts a run
    int current = input[idx];
    int count = 1;

    // Count consecutive equal values
    while (idx + count < n && input[idx + count] == current && count < 255) {
        count++;
    }

    // Only first thread of each run writes
    if (idx == 0 || input[idx - 1] != current) {
        int pos = atomicAdd(output_size, 1);
        output[pos] = current;
        lengths[pos] = count;
    }
}

// Simple RLE decompression
__global__ void rle_decompress(const int* compressed, const int* lengths, int* output, int compressed_size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx >= compressed_size) return;

    int value = compressed[idx];
    int length = lengths[idx];

    // Calculate output position
    int out_pos = 0;
    for (int i = 0; i < idx; i++) {
        out_pos += lengths[i];
    }

    // Write decompressed values
    for (int i = 0; i < length; i++) {
        output[out_pos + i] = value;
    }
}

// Simplified LZ77-style compression (finding repeated patterns)
__global__ void find_patterns(const char* input, int* matches, int n, int window_size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx >= n - 3) return;  // Need at least 4 bytes for a pattern

    int best_match_pos = -1;
    int best_match_len = 0;

    // Look back in the window for matches
    int lookback_start = max(0, idx - window_size);
    for (int i = lookback_start; i < idx; i++) {
        int match_len = 0;
        while (match_len < min(window_size, n - idx) &&
               input[i + match_len] == input[idx + match_len]) {
            match_len++;
        }

        if (match_len > best_match_len && match_len >= 4) {
            best_match_len = match_len;
            best_match_pos = i;
        }
    }

    // Store match info (offset << 16 | length)
    matches[idx] = (best_match_pos >= 0) ?
        ((idx - best_match_pos) << 16 | best_match_len) : 0;
}

// Delta encoding (useful for sequential data)
__global__ void delta_encode(const int* input, int* output, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx >= n) return;

    if (idx == 0) {
        output[0] = input[0];
    } else {
        output[idx] = input[idx] - input[idx - 1];
    }
}

// Delta decoding
__global__ void delta_decode(const int* input, int* output, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx >= n) return;

    if (idx == 0) {
        output[0] = input[0];
    } else {
        // Parallel prefix sum for decoding
        int value = input[idx];
        for (int offset = 1; offset < idx && offset < 32; offset *= 2) {
            int temp = 0;
            if (idx >= offset) {
                temp = output[idx - offset];
            }
            __syncthreads();
            if (idx >= offset) {
                value += temp;
            }
            __syncthreads();
        }
        output[idx] = value;
    }
}

// Bit packing for small integers
__global__ void bit_pack_4bit(const uint8_t* input, uint8_t* output, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx * 2 >= n) return;

    uint8_t low = input[idx * 2] & 0x0F;
    uint8_t high = (idx * 2 + 1 < n) ? (input[idx * 2 + 1] & 0x0F) : 0;

    output[idx] = (high << 4) | low;
}

// Bit unpacking
__global__ void bit_unpack_4bit(const uint8_t* input, uint8_t* output, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx >= n) return;

    uint8_t packed = input[idx];
    output[idx * 2] = packed & 0x0F;
    if (idx * 2 + 1 < n * 2) {
        output[idx * 2 + 1] = (packed >> 4) & 0x0F;
    }
}

// Simple entropy calculation (for compression estimation)
__global__ void calculate_entropy(const int* input, float* entropy, int n, int num_symbols) {
    __shared__ int histogram[256];

    int tid = threadIdx.x;
    if (tid < 256) {
        histogram[tid] = 0;
    }
    __syncthreads();

    // Build histogram
    for (int i = tid; i < n; i += blockDim.x) {
        if (input[i] >= 0 && input[i] < 256) {
            atomicAdd(&histogram[input[i]], 1);
        }
    }
    __syncthreads();

    // Calculate entropy (only first thread)
    if (tid == 0) {
        float ent = 0.0f;
        for (int i = 0; i < num_symbols; i++) {
            if (histogram[i] > 0) {
                float prob = float(histogram[i]) / n;
                ent -= prob * log2f(prob);
            }
        }
        *entropy = ent;
    }
}
