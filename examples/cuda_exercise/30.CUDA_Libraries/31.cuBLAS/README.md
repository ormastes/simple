# 🎯 Part 31: cuBLAS - Linear Algebra

**Goal**: Master NVIDIA's highly optimized BLAS library for linear algebra operations on GPUs, achieving production-ready performance for matrix and vector operations.

## Project Structure

```
31.cuBLAS/
├── README.md          - This documentation
├── CMakeLists.txt     - Build configuration
├── src/
│   ├── CMakeLists.txt            - Source build config
│   ├── matrix_multiply_demo.cu   - Matrix multiplication comparison
│   ├── vector_operations.cu      - Level 1 BLAS examples
│   ├── matrix_vector_ops.cu      - Level 2 BLAS examples
│   └── batched_operations.cu     - Batched GEMM examples
└── test/
    ├── CMakeLists.txt                    - Test build config
    └── unit/
        ├── test_cublas_basic.cu          - Basic cuBLAS operations
        ├── test_matrix_multiply.cu       - Matrix multiplication tests
        └── test_batched_operations.cu    - Batched operations tests
```

## Quick Navigation

- [31.1 Introduction to cuBLAS](#311-introduction-to-cublas)
- [31.2 cuBLAS Handle Management](#312-cublas-handle-management)
- [31.3 Level 1 BLAS Operations](#313-level-1-blas-operations)
- [31.4 Level 2 BLAS Operations](#314-level-2-blas-operations)
- [31.5 Level 3 BLAS Operations](#315-level-3-blas-operations)
- [31.6 Matrix Multiplication Performance](#316-matrix-multiplication-performance)
- [31.7 Batched Operations](#317-batched-operations)
- [31.8 Testing](#318-testing)
- [Build & Run](#build--run)
- [Summary](#summary)

---

## **31.1 Introduction to cuBLAS**

cuBLAS is NVIDIA's implementation of the Basic Linear Algebra Subprograms (BLAS) library optimized for CUDA GPUs. It provides highly tuned implementations of fundamental linear algebra operations that serve as building blocks for scientific computing, machine learning, and data analysis applications.

**Why use cuBLAS:**
- **Performance**: Highly optimized implementations often achieving 90-95% of peak GPU throughput
- **Hardware utilization**: Automatically leverages Tensor Cores on compatible GPUs (Volta, Turing, Ampere, Hopper)
- **Maintained**: Continuously updated by NVIDIA to exploit latest hardware features
- **Standard interface**: Follows BLAS naming conventions familiar to scientific computing community

**BLAS Hierarchy:**
- **Level 1**: Vector-vector operations (O(n)) - dot product, scaling, norms
- **Level 2**: Matrix-vector operations (O(n²)) - matrix-vector multiplication
- **Level 3**: Matrix-matrix operations (O(n³)) - matrix multiplication (GEMM)

Level 3 operations are most important for GPU performance because they have the highest compute-to-memory ratio.

---

## **31.2 cuBLAS Handle Management**

cuBLAS operations require a library handle that encapsulates the library context, similar to a database connection or file handle. This handle manages internal state and resources.

**Basic handle lifecycle:**

```cpp
// Example from src/matrix_multiply_demo.cu
#include <cublas_v2.h>
#include "cuda_utils.h"

class CublasHandle {
private:
    cublasHandle_t handle_;

public:
    CublasHandle() {
        cublasStatus_t status = cublasCreate(&handle_);
        if (status != CUBLAS_STATUS_SUCCESS) {
            throw std::runtime_error("Failed to create cuBLAS handle");
        }
    }

    ~CublasHandle() {
        cublasDestroy(handle_);
    }

    // Disable copy, enable move
    CublasHandle(const CublasHandle&) = delete;
    CublasHandle& operator=(const CublasHandle&) = delete;
    CublasHandle(CublasHandle&& other) noexcept : handle_(other.handle_) {
        other.handle_ = nullptr;
    }

    cublasHandle_t get() const { return handle_; }
};
```

**Key Points:**
- Create handle once, reuse for multiple operations
- Handle is not thread-safe - use one per thread or protect with mutex
- Set math mode to enable Tensor Cores: `cublasSetMathMode(handle, CUBLAS_TENSOR_OP_MATH)`
- Source: `src/matrix_multiply_demo.cu:15-40`

---

## **31.3 Level 1 BLAS Operations**

Level 1 BLAS operations work on vectors and have O(n) complexity. These are the building blocks for more complex operations.

**Common Level 1 operations:**

```cpp
// src/vector_operations.cu - Demonstrates Level 1 BLAS operations

// Dot product: result = x^T * y
float cublas_dot(cublasHandle_t handle, int n, const float* x, const float* y) {
    float result;
    cublasSdot(handle, n, x, 1, y, 1, &result);
    return result;
}

// Vector scaling: y = alpha * x
void cublas_scale(cublasHandle_t handle, int n, float alpha, float* x) {
    cublasSscal(handle, n, &alpha, x, 1);
}

// Vector addition: y = alpha * x + y
void cublas_axpy(cublasHandle_t handle, int n, float alpha,
                 const float* x, float* y) {
    cublasSaxpy(handle, n, &alpha, x, 1, y, 1);
}

// L2 norm: result = ||x||_2
float cublas_nrm2(cublasHandle_t handle, int n, const float* x) {
    float result;
    cublasSnrm2(handle, n, x, 1, &result);
    return result;
}
```

**Key Points:**
- Stride parameter (last argument) allows operating on non-contiguous data
- Operations execute asynchronously - synchronize before reading results
- For small vectors (<1000 elements), CPU might be faster due to kernel launch overhead
- Source: `src/vector_operations.cu:20-55`

**Performance Characteristics:**
- Memory bandwidth bound (not compute bound)
- Typical bandwidth: 400-800 GB/s on modern GPUs
- Best for large vectors (>10,000 elements)

---

## **31.4 Level 2 BLAS Operations**

Level 2 BLAS performs matrix-vector operations with O(n²) complexity. The most important is GEMV (General Matrix-Vector multiplication).

**Matrix-vector multiplication:**

```cpp
// src/matrix_vector_ops.cu - Matrix-vector operations

// Matrix-vector multiply: y = alpha * A * x + beta * y
// A is m x n matrix in column-major order
void cublas_gemv(cublasHandle_t handle,
                 int m, int n,
                 float alpha,
                 const float* A, int lda,
                 const float* x,
                 float beta,
                 float* y) {
    cublasSgemv(handle,
                CUBLAS_OP_N,     // No transpose
                m, n,
                &alpha,
                A, lda,          // Leading dimension
                x, 1,            // Stride for x
                &beta,
                y, 1);           // Stride for y
}

// Transpose matrix-vector: y = alpha * A^T * x + beta * y
void cublas_gemv_transpose(cublasHandle_t handle,
                           int m, int n,
                           float alpha,
                           const float* A, int lda,
                           const float* x,
                           float beta,
                           float* y) {
    cublasSgemv(handle,
                CUBLAS_OP_T,     // Transpose
                m, n,
                &alpha,
                A, lda,
                x, 1,
                &beta,
                y, 1);
}
```

**Key Points:**
- cuBLAS uses **column-major** order (Fortran convention), different from C's row-major
- Leading dimension (lda) is the stride between columns, usually equals number of rows
- Operations can accumulate: `beta != 0` allows adding to existing result
- Source: `src/matrix_vector_ops.cu:15-60`

**Performance Tips:**
- For row-major matrices, use transpose operation
- Larger matrices (>1024 elements) benefit more from GPU
- Consider memory layout - column-major is faster for cuBLAS

---

## **31.5 Level 3 BLAS Operations**

Level 3 BLAS performs matrix-matrix operations with O(n³) complexity. GEMM (General Matrix Multiply) is the most critical operation for GPU computing.

**Matrix multiplication (GEMM):**

```cpp
// src/matrix_multiply_demo.cu - Matrix multiplication with cuBLAS

// Matrix multiply: C = alpha * A * B + beta * C
// A is m x k, B is k x n, C is m x n (all column-major)
void cublas_gemm(cublasHandle_t handle,
                 int m, int n, int k,
                 float alpha,
                 const float* A, int lda,
                 const float* B, int ldb,
                 float beta,
                 float* C, int ldc) {
    cublasSgemm(handle,
                CUBLAS_OP_N, CUBLAS_OP_N,  // No transpose
                m, n, k,
                &alpha,
                A, lda,
                B, ldb,
                &beta,
                C, ldc);
}

// Example usage:
void matrix_multiply_example() {
    const int M = 2048, N = 2048, K = 2048;

    // Allocate matrices
    float *d_A = cuda_malloc<float>(M * K);
    float *d_B = cuda_malloc<float>(K * N);
    float *d_C = cuda_malloc<float>(M * N);

    // Initialize data (not shown)

    CublasHandle handle;
    cublasSetMathMode(handle.get(), CUBLAS_TENSOR_OP_MATH);

    // Perform: C = A * B
    float alpha = 1.0f, beta = 0.0f;
    cublas_gemm(handle.get(), M, N, K, alpha,
                d_A, M, d_B, K, beta, d_C, M);

    cudaDeviceSynchronize();

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}
```

**Key Points:**
- GEMM is the most important operation for deep learning and scientific computing
- Achieves highest performance on GPU (thousands of GFLOPS)
- Tensor Cores provide massive speedup for mixed precision (FP16)
- Source: `src/matrix_multiply_demo.cu:45-95`

---

## **31.6 Matrix Multiplication Performance**

This section compares custom CUDA kernels with cuBLAS to demonstrate the library's performance advantages.

**Performance comparison (2048x2048 matrix):**

```cpp
// src/matrix_multiply_demo.cu - Performance benchmarking

#include "cuda_timer.h"

void benchmark_matmul() {
    const int N = 2048;
    const int size = N * N;

    // Allocate and initialize matrices
    float *d_A = cuda_malloc<float>(size);
    float *d_B = cuda_malloc<float>(size);
    float *d_C_custom = cuda_malloc<float>(size);
    float *d_C_cublas = cuda_malloc<float>(size);

    // Initialize with random data
    initialize_random(d_A, size);
    initialize_random(d_B, size);

    CublasHandle handle;
    CudaTimer timer;

    // Benchmark custom kernel
    dim3 block(16, 16);
    dim3 grid((N + 15) / 16, (N + 15) / 16);

    timer.start();
    matmul_naive<<<grid, block>>>(d_C_custom, d_A, d_B, N);
    timer.stop();
    float custom_time = timer.elapsed_ms();
    float custom_gflops = (2.0f * N * N * N) / (custom_time * 1e6);

    // Benchmark cuBLAS
    float alpha = 1.0f, beta = 0.0f;

    timer.start();
    cublasSgemm(handle.get(), CUBLAS_OP_N, CUBLAS_OP_N,
                N, N, N, &alpha, d_A, N, d_B, N, &beta, d_C_cublas, N);
    timer.stop();
    float cublas_time = timer.elapsed_ms();
    float cublas_gflops = (2.0f * N * N * N) / (cublas_time * 1e6);

    printf("Custom kernel: %.2f GFLOPS (%.3f ms)\n", custom_gflops, custom_time);
    printf("cuBLAS:        %.2f GFLOPS (%.3f ms)\n", cublas_gflops, cublas_time);
    printf("Speedup:       %.2fx\n", cublas_gflops / custom_gflops);

    // Cleanup
    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C_custom);
    cuda_free(d_C_cublas);
}
```

**Expected Output (RTX 3090):**
```
Custom kernel: 520 GFLOPS (33.12 ms)
cuBLAS:        8,450 GFLOPS (2.04 ms)
Speedup:       16.25x
```

**Why cuBLAS is faster:**
- Optimized for specific GPU architecture
- Uses Tensor Cores for mixed precision
- Advanced tiling and memory access patterns
- Register blocking and instruction-level optimizations

Source: `src/matrix_multiply_demo.cu:100-160`

---

## **31.7 Batched Operations**

Batched operations perform the same operation on multiple independent matrices, improving GPU utilization for small matrices.

**Batched matrix multiplication:**

```cpp
// src/batched_operations.cu - Batched GEMM operations

// Batch of matrix multiplications: C[i] = A[i] * B[i] for i = 0..batch_count-1
void cublas_gemm_batched(cublasHandle_t handle,
                         int m, int n, int k,
                         float alpha,
                         const float** A_array, int lda,
                         const float** B_array, int ldb,
                         float beta,
                         float** C_array, int ldc,
                         int batch_count) {
    cublasSgemmBatched(handle,
                       CUBLAS_OP_N, CUBLAS_OP_N,
                       m, n, k,
                       &alpha,
                       A_array, lda,
                       B_array, ldb,
                       &beta,
                       C_array, ldc,
                       batch_count);
}

// Example: Multiply 100 small 128x128 matrices
void batched_example() {
    const int M = 128, N = 128, K = 128;
    const int batch_count = 100;
    const int matrix_size = M * K;

    // Allocate batch of matrices
    std::vector<float*> h_A_ptrs(batch_count);
    std::vector<float*> h_B_ptrs(batch_count);
    std::vector<float*> h_C_ptrs(batch_count);

    for (int i = 0; i < batch_count; i++) {
        h_A_ptrs[i] = cuda_malloc<float>(M * K);
        h_B_ptrs[i] = cuda_malloc<float>(K * N);
        h_C_ptrs[i] = cuda_malloc<float>(M * N);
        // Initialize matrices (not shown)
    }

    // Copy pointer arrays to device
    float** d_A_ptrs = cuda_malloc<float*>(batch_count);
    float** d_B_ptrs = cuda_malloc<float*>(batch_count);
    float** d_C_ptrs = cuda_malloc<float*>(batch_count);

    cudaMemcpy(d_A_ptrs, h_A_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B_ptrs, h_B_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);
    cudaMemcpy(d_C_ptrs, h_C_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);

    CublasHandle handle;
    float alpha = 1.0f, beta = 0.0f;

    cublas_gemm_batched(handle.get(), M, N, K, alpha,
                        const_cast<const float**>(d_A_ptrs), M,
                        const_cast<const float**>(d_B_ptrs), K,
                        beta, d_C_ptrs, M, batch_count);

    cudaDeviceSynchronize();

    // Cleanup (not shown)
}
```

**Key Points:**
- Batched operations launch single kernel for all matrices
- More efficient than loop of individual operations
- Ideal for small matrices (<512x512) in large batches
- Alternative: `cublasSgemmStridedBatched` for uniformly spaced matrices in memory
- Source: `src/batched_operations.cu:20-90`

**Performance comparison (100x 128x128 matrices):**
- Individual GEMM calls: ~15 ms
- Batched GEMM: ~2 ms
- Speedup: ~7.5x

---

## **31.8 Testing**

Comprehensive tests validate cuBLAS operations for correctness and performance.

### **31.8.1 Unit Tests with GpuTest**

Tests use the `GpuTest` base class for automatic CUDA setup. Available in `test/unit/`.

```cpp
// test/unit/test_cublas_basic.cu
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <cublas_v2.h>

class CublasBasicTest : public GpuTest {
protected:
    cublasHandle_t handle;

    void SetUp() override {
        GpuTest::SetUp();
        cublasCreate(&handle);
    }

    void TearDown() override {
        cublasDestroy(handle);
        GpuTest::TearDown();
    }
};

TEST_F(CublasBasicTest, DotProduct) {
    const int n = 1024;
    float* d_x = cuda_malloc<float>(n);
    float* d_y = cuda_malloc<float>(n);

    // Initialize with ones
    std::vector<float> ones(n, 1.0f);
    cudaMemcpy(d_x, ones.data(), n * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_y, ones.data(), n * sizeof(float), cudaMemcpyHostToDevice);

    float result;
    cublasSdot(handle, n, d_x, 1, d_y, 1, &result);
    cudaDeviceSynchronize();

    EXPECT_FLOAT_EQ(result, 1024.0f);

    cuda_free(d_x);
    cuda_free(d_y);
}

TEST_F(CublasBasicTest, VectorScaling) {
    const int n = 100;
    float* d_x = cuda_malloc<float>(n);

    // Initialize with 2.0
    std::vector<float> data(n, 2.0f);
    cudaMemcpy(d_x, data.data(), n * sizeof(float), cudaMemcpyHostToDevice);

    float alpha = 3.0f;
    cublasSscal(handle, n, &alpha, d_x, 1);
    cudaDeviceSynchronize();

    // Read back
    cudaMemcpy(data.data(), d_x, n * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < n; i++) {
        EXPECT_FLOAT_EQ(data[i], 6.0f);
    }

    cuda_free(d_x);
}
```

### **31.8.2 Matrix Multiplication Tests**

```cpp
// test/unit/test_matrix_multiply.cu
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <cublas_v2.h>

class CublasMatmulTest : public GpuTest {
protected:
    cublasHandle_t handle;

    void SetUp() override {
        GpuTest::SetUp();
        cublasCreate(&handle);
    }

    void TearDown() override {
        cublasDestroy(handle);
        GpuTest::TearDown();
    }

    // Helper: CPU reference implementation
    void cpu_gemm(const float* A, const float* B, float* C,
                  int m, int n, int k) {
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
                float sum = 0.0f;
                for (int p = 0; p < k; p++) {
                    sum += A[i * k + p] * B[p * n + j];
                }
                C[i * n + j] = sum;
            }
        }
    }
};

TEST_F(CublasMatmulTest, SmallMatrixMultiply) {
    const int M = 64, N = 64, K = 64;

    // Host matrices (row-major)
    std::vector<float> h_A(M * K);
    std::vector<float> h_B(K * N);
    std::vector<float> h_C_ref(M * N);
    std::vector<float> h_C_gpu(M * N);

    // Initialize with random values
    for (int i = 0; i < M * K; i++) h_A[i] = static_cast<float>(rand()) / RAND_MAX;
    for (int i = 0; i < K * N; i++) h_B[i] = static_cast<float>(rand()) / RAND_MAX;

    // CPU reference
    cpu_gemm(h_A.data(), h_B.data(), h_C_ref.data(), M, N, K);

    // GPU computation (need to convert to column-major)
    // For simplicity, we use transpose flags to work with row-major
    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice);

    float alpha = 1.0f, beta = 0.0f;

    // For row-major C = A * B, use column-major C^T = B^T * A^T
    cublasSgemm(handle, CUBLAS_OP_N, CUBLAS_OP_N,
                N, M, K,
                &alpha,
                d_B, N,  // B^T
                d_A, K,  // A^T
                &beta,
                d_C, N);

    cudaMemcpy(h_C_gpu.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    // Verify results
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C_ref[i], h_C_gpu[i], 1e-3f);
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}
```

### **31.8.3 Running Tests**

```bash
# Build tests
cd build
ninja

# Run all cuBLAS tests
ctest -R cublas -V

# Run with profiling
ninja run_nsys_31_cuBLAS_test

# Run specific test
./30.CUDA_Libraries/31.cuBLAS/test/31_cuBLAS_test --gtest_filter="CublasMatmulTest.*"
```

Source: `test/unit/test_cublas_basic.cu`, `test/unit/test_matrix_multiply.cu`

---

## Build & Run

### Prerequisites
- CUDA Toolkit 13.0+
- CMake 3.18+
- Ninja build system
- GPU with compute capability 7.0+ (for Tensor Cores)

### Build Instructions

```bash
# From repository root
cd build
cmake --preset linux-ninja-debug  # or linux-ninja-release
ninja

# Run demo
./30.CUDA_Libraries/31.cuBLAS/src/31_cuBLAS_demo

# Run tests
ctest -R 31_cuBLAS

# Profile with nsys
ninja run_nsys_31_cuBLAS_demo
```

### Expected Output

```
=== cuBLAS Performance Demo ===

Vector Operations (n=1048576):
  Dot product: 1048576.00 (0.15 ms, 27.9 GB/s)
  Vector scaling: 0.12 ms, 34.9 GB/s

Matrix-Vector Operations (2048x2048):
  GEMV: 0.45 ms, 18.6 GFLOPS

Matrix Multiplication (2048x2048x2048):
  Custom kernel: 520 GFLOPS (33.12 ms)
  cuBLAS FP32:   8,450 GFLOPS (2.04 ms)
  cuBLAS FP16:   42,100 GFLOPS (0.41 ms)
  Tensor Core speedup: 81x over custom kernel

Batched Operations (100x 128x128):
  Individual calls: 15.2 ms
  Batched API: 2.1 ms
  Speedup: 7.2x
```

---

## Summary

### **Key Takeaways**

1. **cuBLAS provides production-ready performance** - Achieves 90-95% of theoretical peak with minimal effort
2. **Tensor Cores deliver massive speedup** - 40+ TFLOPS for mixed precision on Ampere GPUs
3. **Batched operations improve efficiency** - Single kernel launch for multiple small matrices
4. **Column-major layout is critical** - Matches Fortran convention for optimal performance

### **Performance Metrics**

| Operation | Custom Kernel | cuBLAS FP32 | cuBLAS FP16 (Tensor Cores) |
|-----------|---------------|-------------|----------------------------|
| GEMM 2048³ | 520 GFLOPS | 8,450 GFLOPS | 42,100 GFLOPS |
| Efficiency | 3% of peak | 48% of peak | 87% of peak |

### **Common Errors & Solutions**

| Error | Cause | Solution |
|-------|-------|----------|
| Wrong results | Row-major vs column-major confusion | Use transpose flags or convert layout |
| Poor performance | Not using Tensor Cores | Call `cublasSetMathMode(CUBLAS_TENSOR_OP_MATH)` |
| Segmentation fault | Invalid leading dimension | Ensure `lda >= rows` in column-major |

### **Next Steps**

- 📚 Continue to [Part 32: cuFFT](../32.cuFFT/README.md) for Fast Fourier Transforms
- 🔧 Experiment with mixed precision in `src/batched_operations.cu`
- 📊 Profile your own matrix sizes with `ninja run_nsys_31_cuBLAS_demo`

### **References**

- [cuBLAS Documentation](https://docs.nvidia.com/cuda/cublas/)
- [BLAS Quick Reference](https://www.netlib.org/blas/blasqr.pdf)
- [Tensor Core Programming Guide](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#wmma)
