/**
 * Dynamic Parallelism Core Kernels
 *
 * Demonstrates recursive kernel launches and dynamic work generation:
 * - Recursive quicksort
 * - Adaptive histogram
 * - Binary tree traversal
 * - Dynamic workload partitioning
 *
 * Requirements:
 * - Compute Capability 3.5+
 * - Compile with -rdc=true (relocatable device code)
 * - Link with cudadevrt library
 */

#include <cuda_runtime.h>
#include <cuda_device_runtime_api.h>  // For device-side CUDA runtime API
#include <stdio.h>

// Maximum recursion depth to prevent stack overflow
#define MAX_DEPTH 16

// ============================================================================
// Recursive Quicksort
// ============================================================================

/**
 * Partition function for quicksort
 * Returns the pivot index after partitioning
 */
__device__ int partition(int* data, int left, int right) {
    int pivot = data[right];
    int i = left - 1;

    for (int j = left; j < right; j++) {
        if (data[j] <= pivot) {
            i++;
            // Swap data[i] and data[j]
            int temp = data[i];
            data[i] = data[j];
            data[j] = temp;
        }
    }

    // Swap data[i+1] and data[right] (pivot)
    int temp = data[i + 1];
    data[i + 1] = data[right];
    data[right] = temp;

    return i + 1;
}

/**
 * Recursive quicksort using dynamic parallelism
 *
 * Each recursive call launches a new kernel for left and right partitions
 * Stops recursion at MAX_DEPTH or when partition size is small
 */
__global__ void quicksort_dynamic(int* data, int left, int right, int depth) {
    // Base case: single thread does the work
    if (threadIdx.x != 0 || blockIdx.x != 0) return;

    if (left >= right || depth >= MAX_DEPTH) return;

    // Partition the array
    int pivot_idx = partition(data, left, right);

    // Launch child kernels for left and right partitions
    if (depth < MAX_DEPTH - 1) {
        // Sort left partition
        if (pivot_idx - 1 > left) {
            quicksort_dynamic<<<1, 1>>>(data, left, pivot_idx - 1, depth + 1);
        }

        // Sort right partition
        if (pivot_idx + 1 < right) {
            quicksort_dynamic<<<1, 1>>>(data, pivot_idx + 1, right, depth + 1);
        }

        // Note: Device-side sync not available in CUDA 13.0
        // Parent kernel implicitly waits for children on same stream
    }
}

// ============================================================================
// Adaptive Histogram with Dynamic Parallelism
// ============================================================================

/**
 * Child kernel for computing histogram of a sub-range
 */
__global__ void histogram_child(const int* data, int* histogram,
                                 int start, int end, int num_bins) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    int idx = start + tid;

    if (idx < end) {
        int value = data[idx];
        int bin = value % num_bins;
        atomicAdd(&histogram[bin], 1);
    }
}

/**
 * Parent kernel that dynamically launches child kernels based on workload
 *
 * Adaptively partitions work: small ranges processed directly,
 * large ranges spawn child kernels
 */
__global__ void histogram_adaptive(const int* data, int* histogram,
                                    int n, int num_bins, int threshold) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;

    // Only thread 0 of block 0 does the partitioning
    if (tid == 0) {
        if (n <= threshold) {
            // Small workload: process directly
            for (int i = 0; i < n; i++) {
                int bin = data[i] % num_bins;
                atomicAdd(&histogram[bin], 1);
            }
        } else {
            // Large workload: partition and launch child kernels
            int chunk_size = (n + 3) / 4;  // Split into 4 chunks

            for (int i = 0; i < 4; i++) {
                int start = i * chunk_size;
                int end = min(start + chunk_size, n);

                if (start < end) {
                    int threads = min(256, end - start);
                    int blocks = (end - start + threads - 1) / threads;

                    histogram_child<<<blocks, threads>>>(
                        data, histogram, start, end, num_bins);
                }
            }

            // Note: No explicit sync needed - parent kernel waits for children
        }
    }
}

// ============================================================================
// Binary Tree Traversal with Dynamic Parallelism
// ============================================================================

/**
 * Binary tree node structure
 */
struct TreeNode {
    int value;
    int left_child;   // Index of left child (-1 if none)
    int right_child;  // Index of right child (-1 if none)
};

/**
 * Recursive tree traversal using dynamic parallelism
 *
 * Each node spawns two child kernels for left and right subtrees
 */
__global__ void tree_traverse(TreeNode* nodes, int* output,
                               int node_idx, int* counter, int depth) {
    if (threadIdx.x != 0 || blockIdx.x != 0) return;

    if (node_idx == -1 || depth >= MAX_DEPTH) return;

    TreeNode node = nodes[node_idx];

    // Process current node
    int pos = atomicAdd(counter, 1);
    output[pos] = node.value;

    // Launch child kernels for left and right children
    if (node.left_child != -1) {
        tree_traverse<<<1, 1>>>(nodes, output, node.left_child, counter, depth + 1);
    }

    if (node.right_child != -1) {
        tree_traverse<<<1, 1>>>(nodes, output, node.right_child, counter, depth + 1);
    }

    // Note: No explicit sync needed - parent kernel waits for children
}

// ============================================================================
// Dynamic Work Generation
// ============================================================================

/**
 * Worker kernel that processes a range of data
 */
__global__ void worker_kernel(int* data, int start, int end) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    int idx = start + tid;

    if (idx < end) {
        data[idx] = data[idx] * 2 + 1;
    }
}

/**
 * Parent kernel that dynamically generates work based on data characteristics
 *
 * Analyzes data and spawns appropriate number of child kernels
 */
__global__ void dynamic_work_generator(int* data, int n, int min_chunk_size) {
    // Only one thread does the work generation
    if (threadIdx.x != 0 || blockIdx.x != 0) return;

    // Determine number of chunks based on data size
    int num_chunks = (n + min_chunk_size - 1) / min_chunk_size;
    int chunk_size = (n + num_chunks - 1) / num_chunks;

    for (int i = 0; i < num_chunks; i++) {
        int start = i * chunk_size;
        int end = min(start + chunk_size, n);

        if (start < end) {
            int threads = 256;
            int blocks = (end - start + threads - 1) / threads;

            worker_kernel<<<blocks, threads>>>(data, start, end);
        }
    }

    // Note: No explicit sync needed - parent kernel waits for children
}

// ============================================================================
// Nested Parallelism for Matrix Operations
// ============================================================================

/**
 * Child kernel for matrix row processing
 */
__global__ void matrix_row_kernel(float* matrix, int row, int cols, float scale) {
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (col < cols) {
        matrix[row * cols + col] *= scale;
    }
}

/**
 * Parent kernel that launches one child kernel per matrix row
 *
 * Demonstrates row-wise parallel processing with dynamic launches
 */
__global__ void matrix_process_rows(float* matrix, int rows, int cols, float scale) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < rows) {
        // Launch child kernel for this row
        int threads = 256;
        int blocks = (cols + threads - 1) / threads;

        matrix_row_kernel<<<blocks, threads>>>(matrix, row, cols, scale);

        // Note: No explicit sync needed - parent kernel waits for children
    }
}

// ============================================================================
// Recursive Reduction with Dynamic Parallelism
// ============================================================================

/**
 * Simple reduction kernel (single-level)
 *
 * Note: A fully recursive reduction with dynamic parallelism requires complex
 * synchronization patterns. This simplified version demonstrates reduction
 * without the recursive component for stability.
 */
__global__ void reduce_simple(float* data, float* output, int n) {
    __shared__ float sdata[256];

    int tid = threadIdx.x;
    int gid = blockIdx.x * blockDim.x + threadIdx.x;

    // Load data into shared memory
    sdata[tid] = (gid < n) ? data[gid] : 0.0f;
    __syncthreads();

    // Reduce within block
    for (int s = blockDim.x / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    // Thread 0 writes block result
    if (tid == 0) {
        output[blockIdx.x] = sdata[0];
    }
}
