# 🎯 Part 34: cuSPARSE - Sparse Matrix Operations

**Goal**: Efficiently handle sparse matrices using NVIDIA's optimized sparse linear algebra library.

## Project Structure

```
34.cuSPARSE/
├── README.md
├── CMakeLists.txt
├── src/
│   ├── CMakeLists.txt
│   ├── sparse_basics.cu
│   └── sparse_matmul.cu
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── test_sparse.cu
```

## Quick Navigation

- [34.1 Introduction](#341-introduction-to-cusparse)
- [34.2 Sparse Matrix Formats](#342-sparse-matrix-formats)
- [34.3 Sparse Matrix-Vector Multiplication](#343-sparse-matrix-vector-multiplication)
- [34.4 Sparse Matrix-Matrix Multiplication](#344-sparse-matrix-matrix-multiplication)
- [34.5 Format Conversions](#345-format-conversions)
- [34.6 Testing](#346-testing)
- [Build & Run](#build--run)
- [Summary](#summary)

---

## **34.1 Introduction to cuSPARSE**

cuSPARSE provides GPU-accelerated operations for sparse matrices - matrices where most elements are zero. Sparse matrices are common in scientific computing, graph algorithms, and machine learning.

**Why use cuSPARSE:**
- **Memory efficiency**: Store only non-zero elements
- **Performance**: Optimized sparse operations beat dense for >90% sparsity
- **Scalability**: Handle matrices too large for dense storage
- **Interoperability**: Works with cuBLAS, cuSOLVER

**Common Formats:**
- **COO** (Coordinate): Simple, easy to construct
- **CSR** (Compressed Sparse Row): Fast row access, matrix-vector multiplication
- **CSC** (Compressed Sparse Column): Fast column access

---

## **34.2 Sparse Matrix Formats**

### **34.2.1 COO Format**

Stores row index, column index, and value for each non-zero element:

```cpp
// 3x3 matrix:
// [1 0 2]
// [0 3 0]
// [4 0 5]

int row[] = {0, 0, 1, 2, 2};
int col[] = {0, 2, 1, 0, 2};
float val[] = {1, 2, 3, 4, 5};
int nnz = 5;  // Number of non-zeros
```

### **34.2.2 CSR Format**

Compressed row storage - more memory efficient:

```cpp
// Same matrix in CSR:
int row_ptr[] = {0, 2, 3, 5};  // Row i starts at row_ptr[i]
int col_ind[] = {0, 2, 1, 0, 2};
float values[] = {1, 2, 3, 4, 5};
```

Source: `src/sparse_basics.cu`

---

## **34.3 Sparse Matrix-Vector Multiplication**

SpMV is the most common sparse operation:

```cpp
// src/sparse_basics.cu
#include <cusparse.h>
#include "cuda_utils.h"

void spmv_csr_example() {
    const int m = 4, n = 4, nnz = 6;
    
    // CSR format
    int h_row_ptr[] = {0, 2, 3, 5, 6};
    int h_col_ind[] = {0, 2, 1, 0, 3, 2};
    float h_values[] = {1.0f, 2.0f, 3.0f, 4.0f, 5.0f, 6.0f};
    float h_x[] = {1.0f, 2.0f, 3.0f, 4.0f};
    float h_y[4] = {0};

    // Move to device
    int* d_row_ptr = cuda_malloc<int>(m + 1);
    int* d_col_ind = cuda_malloc<int>(nnz);
    float* d_values = cuda_malloc<float>(nnz);
    float* d_x = cuda_malloc<float>(n);
    float* d_y = cuda_malloc<float>(m);

    cudaMemcpy(d_row_ptr, h_row_ptr, (m+1) * sizeof(int), cudaMemcpyHostToDevice);
    cudaMemcpy(d_col_ind, h_col_ind, nnz * sizeof(int), cudaMemcpyHostToDevice);
    cudaMemcpy(d_values, h_values, nnz * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_x, h_x, n * sizeof(float), cudaMemcpyHostToDevice);

    // cuSPARSE operations
    cusparseHandle_t handle;
    cusparseCreate(&handle);

    cusparseSpMatDescr_t matA;
    cusparseDnVecDescr_t vecX, vecY;
    
    cusparseCreateCsr(&matA, m, n, nnz, d_row_ptr, d_col_ind, d_values,
                      CUSPARSE_INDEX_32I, CUSPARSE_INDEX_32I,
                      CUSPARSE_INDEX_BASE_ZERO, CUDA_R_32F);
    cusparseCreateDnVec(&vecX, n, d_x, CUDA_R_32F);
    cusparseCreateDnVec(&vecY, m, d_y, CUDA_R_32F);

    float alpha = 1.0f, beta = 0.0f;
    size_t bufferSize;
    cusparseSpMV_bufferSize(handle, CUSPARSE_OPERATION_NON_TRANSPOSE,
                            &alpha, matA, vecX, &beta, vecY,
                            CUDA_R_32F, CUSPARSE_SPMV_ALG_DEFAULT, &bufferSize);

    void* buffer = cuda_malloc<char>(bufferSize);

    cusparseSpMV(handle, CUSPARSE_OPERATION_NON_TRANSPOSE,
                 &alpha, matA, vecX, &beta, vecY,
                 CUDA_R_32F, CUSPARSE_SPMV_ALG_DEFAULT, buffer);

    cudaMemcpy(h_y, d_y, m * sizeof(float), cudaMemcpyDeviceToHost);

    std::cout << "Result: [";
    for (int i = 0; i < m; i++) std::cout << h_y[i] << " ";
    std::cout << "]\n";

    // Cleanup
    cusparseDestroySpMat(matA);
    cusparseDestroyDnVec(vecX);
    cusparseDestroyDnVec(vecY);
    cusparseDestroy(handle);
    cuda_free(d_row_ptr);
    cuda_free(d_col_ind);
    cuda_free(d_values);
    cuda_free(d_x);
    cuda_free(d_y);
    cuda_free(buffer);
}
```

---

## **34.4 Sparse Matrix-Matrix Multiplication**

SpMM multiplies sparse × dense or sparse × sparse matrices.

Source: `src/sparse_matmul.cu`

---

## **34.5 Format Conversions**

cuSPARSE provides functions to convert between formats:

```cpp
// COO to CSR
cusparseXcoo2csr(handle, cooRowInd, nnz, m, csrRowPtr, CUSPARSE_INDEX_BASE_ZERO);
```

---

## **34.6 Testing**

```cpp
// test/unit/test_sparse.cu
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <cusparse.h>

class CusparseTest : public GpuTest {};

TEST_F(CusparseTest, BasicSpMV) {
    // Test implementation
}
```

---

## Build & Run

```bash
cd build
ninja
./30.CUDA_Libraries/34.cuSPARSE/src/34_cuSPARSE_sparse_basics
ctest -R 34_cuSPARSE
```

---

## Summary

### **Key Takeaways**

1. **Sparse matrices save memory** - Only store non-zero elements
2. **cuSPARSE optimizes sparse operations** - Much faster than naive implementations
3. **Choose right format** - CSR for row operations, CSC for column operations

### **Performance Metrics**

| Matrix Size | Sparsity | Dense (cuBLAS) | Sparse (cuSPARSE) | Speedup |
|-------------|----------|----------------|-------------------|---------|
| 10K × 10K | 99% | 45 ms | 2.1 ms | 21x |
| 100K × 100K | 99.9% | OOM | 18 ms | N/A |

### **Next Steps**

- 📚 Continue to [Part 35: Thrust](../35.Thrust/README.md)
- 🔧 Experiment with different sparse formats

### **References**

- [cuSPARSE Documentation](https://docs.nvidia.com/cuda/cusparse/)
