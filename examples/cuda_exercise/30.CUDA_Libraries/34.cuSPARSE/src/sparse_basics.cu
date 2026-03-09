#include <cusparse.h>
#include "cuda_utils.h"
#include <iostream>
#include <memory>

int main() {
    std::cout << "=== cuSPARSE Sparse Matrix-Vector Multiplication ===\n";

    const int m = 4, n = 4, nnz = 6;
    
    int h_row_ptr[] = {0, 2, 3, 5, 6};
    int h_col_ind[] = {0, 2, 1, 0, 3, 2};
    float h_values[] = {1.0f, 2.0f, 3.0f, 4.0f, 5.0f, 6.0f};
    float h_x[] = {1.0f, 2.0f, 3.0f, 4.0f};
    float h_y[4] = {0};

    int* d_row_ptr = cuda_malloc<int>(m + 1);
    int* d_col_ind = cuda_malloc<int>(nnz);
    float* d_values = cuda_malloc<float>(nnz);
    float* d_x = cuda_malloc<float>(n);
    float* d_y = cuda_malloc<float>(m);

    cudaMemcpy(d_row_ptr, h_row_ptr, (m+1) * sizeof(int), cudaMemcpyHostToDevice);
    cudaMemcpy(d_col_ind, h_col_ind, nnz * sizeof(int), cudaMemcpyHostToDevice);
    cudaMemcpy(d_values, h_values, nnz * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_x, h_x, n * sizeof(float), cudaMemcpyHostToDevice);

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

    std::cout << "Matrix-vector product result: [";
    for (int i = 0; i < m; i++) std::cout << h_y[i] << " ";
    std::cout << "]\n";

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

    std::cout << "Demo completed successfully!\n";
    return 0;
}
