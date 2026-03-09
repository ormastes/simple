/**
 * @file torch_matmul_api.cpp
 * @brief C API implementation for matrix multiplication
 *
 * Validates tensor descriptors and delegates to the tiled CUDA kernel launcher.
 * This function is exported with C linkage so it can be loaded via Python ctypes.
 */

#include "torch_api.h"
#include "matmul_kernel.h"
#include <cuda_runtime.h>
#include <cstdio>

/**
 * @brief Validate that a tensor descriptor is well-formed
 *
 * @param desc  Tensor descriptor to check
 * @param name  Human-readable name for error messages
 * @return TORCH_SUCCESS if valid, TORCH_ERROR_INVALID_ARGUMENT otherwise
 */
static TorchStatus validate_tensor(const TorchTensorDesc* desc, const char* name) {
    if (!desc) {
        fprintf(stderr, "torch_matmul: %s descriptor is NULL\n", name);
        return TORCH_ERROR_INVALID_ARGUMENT;
    }
    if (!desc->data) {
        fprintf(stderr, "torch_matmul: %s data pointer is NULL\n", name);
        return TORCH_ERROR_INVALID_ARGUMENT;
    }
    if (desc->ndim < 2) {
        fprintf(stderr, "torch_matmul: %s must be at least 2-D (got %d)\n", name, desc->ndim);
        return TORCH_ERROR_INVALID_ARGUMENT;
    }
    return TORCH_SUCCESS;
}

extern "C" TorchStatus torch_matmul(TorchTensorDesc* C,
                                     const TorchTensorDesc* A,
                                     const TorchTensorDesc* B) {
    // ---- Input validation ----
    TorchStatus status;
    status = validate_tensor(A, "A");
    if (status != TORCH_SUCCESS) return status;
    status = validate_tensor(B, "B");
    if (status != TORCH_SUCCESS) return status;
    status = validate_tensor(C, "C");
    if (status != TORCH_SUCCESS) return status;

    // Extract dimensions (last two axes are the matrix dimensions)
    int M = static_cast<int>(A->shape[A->ndim - 2]);
    int K_a = static_cast<int>(A->shape[A->ndim - 1]);
    int K_b = static_cast<int>(B->shape[B->ndim - 2]);
    int N = static_cast<int>(B->shape[B->ndim - 1]);

    if (K_a != K_b) {
        fprintf(stderr, "torch_matmul: inner dimensions mismatch A[..,%d] vs B[%d,..]\n",
                K_a, K_b);
        return TORCH_ERROR_INVALID_ARGUMENT;
    }
    int K = K_a;

    // Verify output dimensions
    int C_M = static_cast<int>(C->shape[C->ndim - 2]);
    int C_N = static_cast<int>(C->shape[C->ndim - 1]);
    if (C_M != M || C_N != N) {
        fprintf(stderr, "torch_matmul: output shape [%d,%d] does not match expected [%d,%d]\n",
                C_M, C_N, M, N);
        return TORCH_ERROR_INVALID_ARGUMENT;
    }

    // ---- Launch kernel ----
    launch_tiled_matmul(C->data, A->data, B->data, M, N, K, nullptr);

    cudaError_t err = cudaGetLastError();
    if (err != cudaSuccess) {
        fprintf(stderr, "torch_matmul: CUDA error: %s\n", cudaGetErrorString(err));
        return TORCH_ERROR_CUDA;
    }

    err = cudaDeviceSynchronize();
    if (err != cudaSuccess) {
        fprintf(stderr, "torch_matmul: CUDA sync error: %s\n", cudaGetErrorString(err));
        return TORCH_ERROR_CUDA;
    }

    return TORCH_SUCCESS;
}
