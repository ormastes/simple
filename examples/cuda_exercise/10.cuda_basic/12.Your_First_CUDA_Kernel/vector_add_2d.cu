// vector_add_2d.cu - Complete first CUDA kernel example
// Demonstrates: __global__, __device__, dim3, memory management, 2D grids
#include <iostream>
#include <cuda_runtime.h>

//==============================================================================
// DEVICE FUNCTIONS (GPU-only helper functions)
//==============================================================================

/**
 * Device function: runs on GPU, callable only from GPU
 * This demonstrates code reuse within device code
 */
__device__ float square(float x) {
    return x * x;
}

//==============================================================================
// KERNEL FUNCTIONS (GPU entry points, callable from CPU)
//==============================================================================

/**
 * Kernel function: runs on GPU, launched from CPU
 * Computes: C[i] = A[i]² + B[i] for all elements
 *
 * @param A Input array A (device memory)
 * @param B Input array B (device memory)
 * @param C Output array C (device memory)
 * @param width Width of 2D grid
 * @param height Height of 2D grid
 */
__global__ void vector_add_2d(const float* A, const float* B, float* C,
                              int width, int height) {
    // Step 1: Calculate this thread's 2D position in the grid
    int x = blockIdx.x * blockDim.x + threadIdx.x;  // Column
    int y = blockIdx.y * blockDim.y + threadIdx.y;  // Row

    // Step 2: Convert 2D position to 1D array index
    // Row-major order: idx = row * width + col
    int i = y * width + x;

    // Step 3: Boundary check to prevent out-of-bounds access
    // Grid may be larger than data due to rounding in block calculation
    if (x < width && y < height) {
        // Step 4: Perform computation
        // Each thread computes exactly one element
        C[i] = square(A[i]) + B[i];
    }
}

//==============================================================================
// HOST CODE (CPU)
//==============================================================================

int main() {
    // Define problem size: 1024x1024 = 1,048,576 elements
    int width = 1024;
    int height = 1024;
    int N = width * height;
    size_t size = N * sizeof(float);

    std::cout << "Computing vector operation on " << N << " elements" << std::endl;
    std::cout << "Grid size: " << width << "x" << height << std::endl;

    //==========================================================================
    // STEP 1: Allocate host (CPU) memory
    //==========================================================================

    float *h_A = (float*)malloc(size);  // h_ prefix = host memory
    float *h_B = (float*)malloc(size);
    float *h_C = (float*)malloc(size);

    if (!h_A || !h_B || !h_C) {
        std::cerr << "Host memory allocation failed!" << std::endl;
        return -1;
    }

    //==========================================================================
    // STEP 2: Initialize input data on host
    //==========================================================================

    for (int i = 0; i < N; ++i) {
        h_A[i] = static_cast<float>(i);      // A[i] = i
        h_B[i] = static_cast<float>(2 * i);  // B[i] = 2*i
    }
    std::cout << "Initialized input data" << std::endl;

    //==========================================================================
    // STEP 3: Allocate device (GPU) memory
    //==========================================================================

    float *d_A, *d_B, *d_C;  // d_ prefix = device memory

    cudaError_t err;
    err = cudaMalloc(&d_A, size);
    if (err != cudaSuccess) {
        std::cerr << "cudaMalloc d_A failed: " << cudaGetErrorString(err) << std::endl;
        free(h_A); free(h_B); free(h_C);
        return -1;
    }

    cudaMalloc(&d_B, size);
    cudaMalloc(&d_C, size);
    std::cout << "Allocated GPU memory: " << (size * 3 / (1024*1024)) << " MB" << std::endl;

    //==========================================================================
    // STEP 4: Copy input data from host to device
    //==========================================================================

    cudaMemcpy(d_A, h_A, size, cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B, size, cudaMemcpyHostToDevice);
    std::cout << "Copied input data to GPU" << std::endl;

    //==========================================================================
    // STEP 5: Configure kernel launch parameters
    //==========================================================================

    // Use 16x16 threads per block (256 total threads)
    dim3 threads(16, 16);

    // Calculate number of blocks needed
    // Round up: (width + threads.x - 1) / threads.x ensures we cover all elements
    dim3 blocks(
        (width + threads.x - 1) / threads.x,    // Blocks in x direction
        (height + threads.y - 1) / threads.y    // Blocks in y direction
    );

    std::cout << "Launch config: " << blocks.x << "x" << blocks.y << " blocks, "
              << threads.x << "x" << threads.y << " threads per block" << std::endl;
    std::cout << "Total threads: " << (blocks.x * threads.x * blocks.y * threads.y) << std::endl;

    //==========================================================================
    // STEP 6: Launch kernel
    //==========================================================================

    vector_add_2d<<<blocks, threads>>>(d_A, d_B, d_C, width, height);

    // Check for kernel launch errors
    err = cudaGetLastError();
    if (err != cudaSuccess) {
        std::cerr << "Kernel launch failed: " << cudaGetErrorString(err) << std::endl;
        cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
        free(h_A); free(h_B); free(h_C);
        return -1;
    }

    std::cout << "Kernel launched" << std::endl;

    //==========================================================================
    // STEP 7: Wait for kernel completion and copy results back
    //==========================================================================

    // Wait for all GPU operations to complete
    cudaDeviceSynchronize();
    std::cout << "Kernel completed" << std::endl;

    // Copy results back from device to host
    cudaMemcpy(h_C, d_C, size, cudaMemcpyDeviceToHost);
    std::cout << "Copied results back to CPU" << std::endl;

    //==========================================================================
    // STEP 8: Verify results
    //==========================================================================

    std::cout << "\nVerifying results (first 10 elements):" << std::endl;
    bool correct = true;

    for (int i = 0; i < 10; i++) {
        float expected = h_A[i] * h_A[i] + h_B[i];  // A[i]² + B[i]
        std::cout << "C[" << i << "] = " << h_C[i]
                  << " (expected: " << expected << ")";

        if (h_C[i] != expected) {
            std::cout << " MISMATCH!";
            correct = false;
        }
        std::cout << std::endl;
    }

    if (correct) {
        std::cout << "\n✓ All results correct!" << std::endl;
    } else {
        std::cout << "\n✗ Results incorrect!" << std::endl;
    }

    //==========================================================================
    // STEP 9: Free memory
    //==========================================================================

    cudaFree(d_A);
    cudaFree(d_B);
    cudaFree(d_C);
    free(h_A);
    free(h_B);
    free(h_C);

    std::cout << "\nProgram completed successfully" << std::endl;
    return 0;
}
