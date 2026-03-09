// wmma_basic.cu - Basic Tensor Core (WMMA) demonstration
#include <mma.h>
#include <cuda_runtime.h>
#include <cuda_fp16.h>
#include "cuda_utils.h"
#include <iostream>
#include <memory>

using namespace nvcuda;

// Simple kernel demonstrating WMMA API
__global__ void wmma_simple_kernel(half* a, half* b, float* c, int M, int N, int K) {
    // Tile using a 32-thread warp
    int warpM = (blockIdx.x * blockDim.x + threadIdx.x) / 32;
    int warpN = (blockIdx.y * blockDim.y + threadIdx.y);

    // Declare fragments for 16x16x16 matrix operation
    wmma::fragment<wmma::matrix_a, 16, 16, 16, half, wmma::row_major> a_frag;
    wmma::fragment<wmma::matrix_b, 16, 16, 16, half, wmma::row_major> b_frag;
    wmma::fragment<wmma::accumulator, 16, 16, 16, float> c_frag;

    // Initialize accumulator to zero
    wmma::fill_fragment(c_frag, 0.0f);

    // Bounds check
    if (warpM < M / 16 && warpN < N / 16) {
        // Load matrices into fragments
        wmma::load_matrix_sync(a_frag, a + warpM * 16 * K, K);
        wmma::load_matrix_sync(b_frag, b + warpN * 16, N);

        // Perform matrix multiply-accumulate
        wmma::mma_sync(c_frag, a_frag, b_frag, c_frag);

        // Store result
        wmma::store_matrix_sync(c + warpM * 16 * N + warpN * 16, c_frag, N, wmma::mem_row_major);
    }
}

int main() {
    std::cout << "=== Tensor Cores (WMMA) Basic Demo ===\n";

    // Check compute capability
    int device;
    cudaGetDevice(&device);
    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, device);
    
    std::cout << "Device: " << prop.name << "\n";
    std::cout << "Compute Capability: " << prop.major << "." << prop.minor << "\n";

    if (prop.major < 7) {
        std::cout << "Tensor Cores require compute capability 7.0+ (Volta or newer)\n";
        return 0;
    }

    // Matrix dimensions (must be multiples of 16 for WMMA)
    const int M = 16, N = 16, K = 16;

    // Allocate host memory
    std::unique_ptr<half[]> h_a(new half[M * K]);
    std::unique_ptr<half[]> h_b(new half[K * N]);
    std::unique_ptr<float[]> h_c(new float[M * N]);

    // Initialize with simple values
    for (int i = 0; i < M * K; i++) h_a[i] = __float2half(1.0f);
    for (int i = 0; i < K * N; i++) h_b[i] = __float2half(1.0f);

    // Allocate device memory
    half* d_a = cuda_malloc<half>(M * K);
    half* d_b = cuda_malloc<half>(K * N);
    float* d_c = cuda_malloc<float>(M * N);

    // Copy to device
    cudaMemcpy(d_a, h_a.get(), M * K * sizeof(half), cudaMemcpyHostToDevice);
    cudaMemcpy(d_b, h_b.get(), K * N * sizeof(half), cudaMemcpyHostToDevice);

    // Launch kernel (one warp for this small example)
    dim3 grid(1, 1);
    dim3 block(32, 1);
    wmma_simple_kernel<<<grid, block>>>(d_a, d_b, d_c, M, N, K);
    CHECK_KERNEL_LAUNCH();

    // Copy result back
    cudaMemcpy(h_c.get(), d_c, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    // Verify result (should be K since all elements are 1)
    std::cout << "Result (should be " << K << " for all elements):\n";
    std::cout << "Sample values: " << h_c[0] << ", " << h_c[M*N-1] << "\n";

    bool correct = true;
    for (int i = 0; i < M * N; i++) {
        if (std::abs(h_c[i] - K) > 0.1f) {
            correct = false;
            break;
        }
    }

    std::cout << "Correctness: " << (correct ? "PASSED" : "FAILED") << "\n";

    // Cleanup
    cuda_free(d_a);
    cuda_free(d_b);
    cuda_free(d_c);

    std::cout << "Demo completed successfully!\n";
    return 0;
}
