/**
 * @file gemm_int8_dp4a.cu
 * @brief INT8 GEMM implementation using DP4A intrinsics (optional)
 */
#include <cuda_runtime.h>
#include <cstdint>

namespace transformer {

/**
 * @brief DP4A dot product of 4 int8 values packed into int32
 *
 * Computes: c += dot(a_bytes, b_bytes) where a_bytes and b_bytes are
 * each 4 int8 values packed into a single int32.
 *
 * @param[in] a Four int8 values packed as int32
 * @param[in] b Four int8 values packed as int32
 * @param[in] c Accumulator
 * @return c + dot(a, b)
 */
__device__ __forceinline__ int dp4a(int a, int b, int c) {
    return __dp4a(a, b, c);
}

/**
 * @brief INT8 GEMM kernel using DP4A intrinsics
 *
 * Computes C[M,N] = A[M,K] * B^T[N,K] where B is stored in column-major
 * (transposed) layout to enable contiguous DP4A access.
 *
 * @param[out] C Output matrix [M, N] in int32
 * @param[in] A Input matrix [M, K] in int8, row-major
 * @param[in] B Input matrix [N, K] in int8, transposed (col-major of [K, N])
 * @param[in] M Number of rows of A and C
 * @param[in] N Number of columns of C (rows of B^T)
 * @param[in] K Inner dimension (must be multiple of 4)
 */
__global__ void gemm_int8_kernel(int32_t* __restrict__ C,
                                  const int8_t* __restrict__ A,
                                  const int8_t* __restrict__ B,
                                  int M, int N, int K) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row >= M || col >= N) return;

    int32_t sum = 0;
    // Process 4 int8 values at a time
    int K4 = K / 4;
    const int* A_int = reinterpret_cast<const int*>(A + row * K);
    const int* B_int = reinterpret_cast<const int*>(B + col * K);  // B is transposed

    for (int k = 0; k < K4; k++) {
        sum = dp4a(A_int[k], B_int[k], sum);
    }

    C[row * N + col] = sum;
}

/**
 * @brief Launch INT8 GEMM using DP4A intrinsics
 * @param[out] C Output matrix [M, N] in int32
 * @param[in] A Input matrix [M, K] in int8
 * @param[in] B Input matrix [N, K] in int8 (transposed)
 * @param[in] M Number of rows
 * @param[in] N Number of columns
 * @param[in] K Inner dimension (must be multiple of 4)
 * @param[in] stream CUDA stream
 */
void gemm_i8_dp4a(int32_t* C, const int8_t* A, const int8_t* B,
                  int M, int N, int K, cudaStream_t stream) {
    dim3 block(16, 16);
    dim3 grid((N + 15) / 16, (M + 15) / 16);
    gemm_int8_kernel<<<grid, block, 0, stream>>>(C, A, B, M, N, K);
}

} // namespace transformer
