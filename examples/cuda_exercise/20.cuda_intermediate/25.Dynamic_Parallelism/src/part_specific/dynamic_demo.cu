/**
 * Dynamic Parallelism Comprehensive Demonstration
 *
 * Shows key use cases for dynamic parallelism:
 * 1. Recursive quicksort
 * 2. Adaptive histogram
 * 3. Binary tree traversal
 * 4. Dynamic work generation
 */

#include <cuda_runtime.h>
#include <stdio.h>
#include <stdlib.h>
#include "cuda_utils.h"

// Include kernel declarations
#include "part_specific/dynamic_kernels.h"

// ============================================================================
// Demo 1: Recursive Quicksort
// ============================================================================

void demo_quicksort() {
    printf("=== Demo 1: Recursive Quicksort ===\n");

    const int N = 1024;
    int *h_data, *d_data;

    CHECK_CUDA(cudaMallocHost(&h_data, N * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_data, N * sizeof(int)));

    // Initialize with random data
    for (int i = 0; i < N; i++) {
        h_data[i] = rand() % 1000;
    }

    CHECK_CUDA(cudaMemcpy(d_data, h_data, N * sizeof(int), cudaMemcpyHostToDevice));

    // Launch quicksort with dynamic parallelism
    CudaTimer timer;
    timer.start();
    quicksort_dynamic<<<1, 1>>>(d_data, 0, N - 1, 0);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());
    timer.stop();

    CHECK_CUDA(cudaMemcpy(h_data, d_data, N * sizeof(int), cudaMemcpyDeviceToHost));

    // Verify sorting
    bool sorted = true;
    for (int i = 0; i < N - 1; i++) {
        if (h_data[i] > h_data[i + 1]) {
            sorted = false;
            break;
        }
    }

    printf("Array size: %d elements\n", N);
    printf("Time: %.3f ms\n", timer.elapsed_ms());
    printf("Result: %s\n", sorted ? "✓ Correctly sorted" : "✗ Sort failed");
    printf("First 10 elements: ");
    for (int i = 0; i < 10; i++) {
        printf("%d ", h_data[i]);
    }
    printf("\n\n");

    cudaFreeHost(h_data);
    cudaFree(d_data);
}

// ============================================================================
// Demo 2: Adaptive Histogram
// ============================================================================

void demo_adaptive_histogram() {
    printf("=== Demo 2: Adaptive Histogram ===\n");

    const int N = 1024 * 1024;
    const int NUM_BINS = 256;
    int *h_data, *h_histogram;
    int *d_data, *d_histogram;

    CHECK_CUDA(cudaMallocHost(&h_data, N * sizeof(int)));
    CHECK_CUDA(cudaMallocHost(&h_histogram, NUM_BINS * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_data, N * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_histogram, NUM_BINS * sizeof(int)));

    // Initialize with random data
    for (int i = 0; i < N; i++) {
        h_data[i] = rand() % NUM_BINS;
    }

    CHECK_CUDA(cudaMemcpy(d_data, h_data, N * sizeof(int), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemset(d_histogram, 0, NUM_BINS * sizeof(int)));

    // Launch adaptive histogram
    CudaTimer timer;
    timer.start();
    histogram_adaptive<<<1, 1>>>(d_data, d_histogram, N, NUM_BINS, 1024);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());
    timer.stop();

    CHECK_CUDA(cudaMemcpy(h_histogram, d_histogram, NUM_BINS * sizeof(int), cudaMemcpyDeviceToHost));

    // Verify total count
    int total = 0;
    for (int i = 0; i < NUM_BINS; i++) {
        total += h_histogram[i];
    }

    printf("Array size: %d elements\n", N);
    printf("Number of bins: %d\n", NUM_BINS);
    printf("Time: %.3f ms\n", timer.elapsed_ms());
    printf("Total count: %d (expected: %d)\n", total, N);
    printf("Result: %s\n", (total == N) ? "✓ Correct" : "✗ Failed");
    printf("Sample bins (0-9): ");
    for (int i = 0; i < 10; i++) {
        printf("%d ", h_histogram[i]);
    }
    printf("\n\n");

    cudaFreeHost(h_data);
    cudaFreeHost(h_histogram);
    cudaFree(d_data);
    cudaFree(d_histogram);
}

// ============================================================================
// Demo 3: Binary Tree Traversal
// ============================================================================

void demo_tree_traversal() {
    printf("=== Demo 3: Binary Tree Traversal ===\n");

    // Create a simple binary tree
    //       0
    //      / \
    //     1   2
    //    / \   \
    //   3   4   5
    const int NUM_NODES = 6;
    TreeNode h_nodes[NUM_NODES] = {
        {0, 1, 2},    // Node 0: left=1, right=2
        {1, 3, 4},    // Node 1: left=3, right=4
        {2, -1, 5},   // Node 2: left=none, right=5
        {3, -1, -1},  // Node 3: leaf
        {4, -1, -1},  // Node 4: leaf
        {5, -1, -1}   // Node 5: leaf
    };

    TreeNode *d_nodes;
    int *d_output, *d_counter;
    int *h_output, h_counter = 0;

    CHECK_CUDA(cudaMalloc(&d_nodes, NUM_NODES * sizeof(TreeNode)));
    CHECK_CUDA(cudaMalloc(&d_output, NUM_NODES * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_counter, sizeof(int)));

    CHECK_CUDA(cudaMallocHost(&h_output, NUM_NODES * sizeof(int)));

    CHECK_CUDA(cudaMemcpy(d_nodes, h_nodes, NUM_NODES * sizeof(TreeNode), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_counter, &h_counter, sizeof(int), cudaMemcpyHostToDevice));

    // Launch tree traversal
    CudaTimer timer;
    timer.start();
    tree_traverse<<<1, 1>>>(d_nodes, d_output, 0, d_counter, 0);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());
    timer.stop();

    CHECK_CUDA(cudaMemcpy(h_output, d_output, NUM_NODES * sizeof(int), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(&h_counter, d_counter, sizeof(int), cudaMemcpyDeviceToHost));

    printf("Number of nodes: %d\n", NUM_NODES);
    printf("Time: %.3f ms\n", timer.elapsed_ms());
    printf("Traversal order: ");
    for (int i = 0; i < h_counter; i++) {
        printf("%d ", h_output[i]);
    }
    printf("\nNodes visited: %d/%d\n\n", h_counter, NUM_NODES);

    cudaFreeHost(h_output);
    cudaFree(d_nodes);
    cudaFree(d_output);
    cudaFree(d_counter);
}

// ============================================================================
// Demo 4: Dynamic Work Generation
// ============================================================================

void demo_dynamic_work() {
    printf("=== Demo 4: Dynamic Work Generation ===\n");

    const int N = 1024 * 256;
    int *h_data, *d_data;

    CHECK_CUDA(cudaMallocHost(&h_data, N * sizeof(int)));
    CHECK_CUDA(cudaMalloc(&d_data, N * sizeof(int)));

    // Initialize
    for (int i = 0; i < N; i++) {
        h_data[i] = i;
    }

    CHECK_CUDA(cudaMemcpy(d_data, h_data, N * sizeof(int), cudaMemcpyHostToDevice));

    // Launch dynamic work generator
    CudaTimer timer;
    timer.start();
    dynamic_work_generator<<<1, 1>>>(d_data, N, 4096);
    CHECK_KERNEL_LAUNCH();
    CHECK_CUDA(cudaDeviceSynchronize());
    timer.stop();

    CHECK_CUDA(cudaMemcpy(h_data, d_data, N * sizeof(int), cudaMemcpyDeviceToHost));

    // Verify transformation (data[i] = i * 2 + 1)
    bool correct = true;
    for (int i = 0; i < N; i++) {
        if (h_data[i] != i * 2 + 1) {
            correct = false;
            break;
        }
    }

    printf("Array size: %d elements\n", N);
    printf("Time: %.3f ms\n", timer.elapsed_ms());
    printf("Result: %s\n", correct ? "✓ Correct transformation" : "✗ Failed");
    printf("\n");

    cudaFreeHost(h_data);
    cudaFree(d_data);
}

// ============================================================================
// Main
// ============================================================================

int main() {
    cudaDeviceProp prop;
    CHECK_CUDA(cudaGetDeviceProperties(&prop, 0));

    printf("╔══════════════════════════════════════════════════════════════╗\n");
    printf("║          Dynamic Parallelism Demonstration                 ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n\n");

    printf("Device: %s\n", prop.name);
    printf("Compute Capability: %d.%d\n", prop.major, prop.minor);

    if (prop.major < 3 || (prop.major == 3 && prop.minor < 5)) {
        printf("\n✗ Error: Dynamic Parallelism requires Compute Capability 3.5 or higher\n");
        printf("  Your device has Compute Capability %d.%d\n", prop.major, prop.minor);
        return 1;
    }

    printf("✓ Dynamic Parallelism supported\n\n");

    printf("═══════════════════════════════════════════════════════════════\n\n");

    // Run demonstrations
    demo_quicksort();
    demo_adaptive_histogram();
    demo_tree_traversal();
    demo_dynamic_work();

    printf("═══════════════════════════════════════════════════════════════\n\n");

    printf("Key Takeaways:\n");
    printf("  1. Dynamic parallelism enables recursive algorithms on GPU\n");
    printf("  2. Child kernels can be launched from parent kernels\n");
    printf("  3. Useful for irregular workloads and tree-based structures\n");
    printf("  4. cudaDeviceSynchronize() ensures child kernel completion\n\n");

    printf("Performance Notes:\n");
    printf("  - Each kernel launch has overhead (~6-8 μs)\n");
    printf("  - Best for irregular, data-dependent workloads\n");
    printf("  - May be slower than iterative approaches for regular workloads\n");
    printf("  - Requires -rdc=true compilation flag\n\n");

    return 0;
}
