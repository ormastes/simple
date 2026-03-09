#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <cusparse.h>
#include "cuda_utils.h"

class CusparseTest : public GpuTest {};

TEST_F(CusparseTest, HandleCreation) {
    cusparseHandle_t handle;
    ASSERT_EQ(cusparseCreate(&handle), CUSPARSE_STATUS_SUCCESS);
    ASSERT_EQ(cusparseDestroy(handle), CUSPARSE_STATUS_SUCCESS);
}

TEST_F(CusparseTest, BasicSpMV) {
    cusparseHandle_t handle;
    cusparseCreate(&handle);

    const int m = 2, n = 2, nnz = 2;
    int h_row_ptr[] = {0, 1, 2};
    int h_col_ind[] = {0, 1};
    float h_values[] = {1.0f, 1.0f};

    int* d_row_ptr = cuda_malloc<int>(m + 1);
    int* d_col_ind = cuda_malloc<int>(nnz);
    float* d_values = cuda_malloc<float>(nnz);

    cudaMemcpy(d_row_ptr, h_row_ptr, (m+1) * sizeof(int), cudaMemcpyHostToDevice);
    cudaMemcpy(d_col_ind, h_col_ind, nnz * sizeof(int), cudaMemcpyHostToDevice);
    cudaMemcpy(d_values, h_values, nnz * sizeof(float), cudaMemcpyHostToDevice);

    cusparseSpMatDescr_t matA;
    cusparseCreateCsr(&matA, m, n, nnz, d_row_ptr, d_col_ind, d_values,
                      CUSPARSE_INDEX_32I, CUSPARSE_INDEX_32I,
                      CUSPARSE_INDEX_BASE_ZERO, CUDA_R_32F);

    cusparseDestroySpMat(matA);
    cusparseDestroy(handle);
    cuda_free(d_row_ptr);
    cuda_free(d_col_ind);
    cuda_free(d_values);
}
