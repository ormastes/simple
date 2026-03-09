/**
 * Dynamic Parallelism Kernel Declarations
 *
 * Header file for dynamic parallelism kernels
 */

#ifndef DYNAMIC_KERNELS_H
#define DYNAMIC_KERNELS_H

#include <cuda_runtime.h>

// Tree node structure for tree traversal
struct TreeNode {
    int value;
    int left_child;   // -1 if no left child
    int right_child;  // -1 if no right child
};

// Kernel declarations
__global__ void quicksort_dynamic(int* data, int left, int right, int depth);
__global__ void histogram_adaptive(const int* data, int* histogram, int n, int num_bins, int threshold);
__global__ void tree_traverse(TreeNode* nodes, int* output, int node_idx, int* counter, int depth);
__global__ void dynamic_work_generator(int* data, int n, int chunk_size);
__global__ void matrix_process_rows(float* matrix, int rows, int cols, float scale);

#endif // DYNAMIC_KERNELS_H
