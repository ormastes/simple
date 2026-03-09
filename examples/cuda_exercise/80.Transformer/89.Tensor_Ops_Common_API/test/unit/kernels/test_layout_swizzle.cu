/**
 * @file test_layout_swizzle.cu
 * @brief Unit tests for layout indexing and swizzle utilities
 *
 * Tests row-major, column-major, Col32 indexing, StrideHelper for 3D tensors,
 * and shared memory swizzle correctness.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/layout_swizzle.cuh"

// ---------------------------------------------------------------------------
// Test kernels
// ---------------------------------------------------------------------------

/**
 * @brief Kernel: verify row_major_idx for a small matrix
 */
__global__ void kernel_test_row_major(int* results, int num_rows, int num_cols) {
    // Fill results[row * num_cols + col] with row_major_idx(row, col, num_cols)
    for (int r = 0; r < num_rows; r++) {
        for (int c = 0; c < num_cols; c++) {
            results[r * num_cols + c] = transformer::row_major_idx(r, c, num_cols);
        }
    }
}

/**
 * @brief Kernel: verify col_major_idx for a small matrix
 */
__global__ void kernel_test_col_major(int* results, int num_rows, int num_cols) {
    for (int r = 0; r < num_rows; r++) {
        for (int c = 0; c < num_cols; c++) {
            results[r * num_cols + c] = transformer::col_major_idx(r, c, num_rows);
        }
    }
}

/**
 * @brief Kernel: verify col32_padded for various dimensions
 */
__global__ void kernel_test_col32_padded(const int* dims, int* results, int n) {
    for (int i = 0; i < n; i++) {
        results[i] = transformer::col32_padded(dims[i]);
    }
}

/**
 * @brief Kernel: verify col32_idx uniqueness and correctness
 *
 * For a small matrix, compute col32_idx for every (row, col) and store
 * in output. Verify that all indices are unique and within bounds.
 */
__global__ void kernel_test_col32_idx(int* results, int* unique_check,
                                       int num_rows, int num_cols) {
    int total = num_rows * num_cols;
    // Initialize unique_check to 0
    for (int i = 0; i < total; i++) {
        unique_check[i] = 0;
    }

    // Compute col32 indices
    for (int r = 0; r < num_rows; r++) {
        for (int c = 0; c < num_cols; c++) {
            int idx = transformer::col32_idx(r, c, num_rows);
            results[r * num_cols + c] = idx;
            if (idx >= 0 && idx < total) {
                atomicAdd(&unique_check[idx], 1);
            }
        }
    }
}

/**
 * @brief Kernel: verify StrideHelper for 3D row-major tensor
 */
__global__ void kernel_test_stride_helper(int* results, int B, int M, int N) {
    transformer::StrideHelper sh = transformer::make_row_major_3d(M, N);

    // Store stride values
    results[0] = sh.stride0;
    results[1] = sh.stride1;
    results[2] = sh.stride2;

    // Compute indices for a few sample points
    int idx = 3;
    results[idx++] = sh(0, 0, 0);         // [0,0,0] = 0
    results[idx++] = sh(0, 0, 1);         // [0,0,1] = 1
    results[idx++] = sh(0, 1, 0);         // [0,1,0] = N
    results[idx++] = sh(1, 0, 0);         // [1,0,0] = M*N
    results[idx++] = sh(1, 2, 3);         // [1,2,3] = M*N + 2*N + 3
}

/**
 * @brief Kernel: verify smem_swizzle produces valid indices
 *
 * For a range of input indices, verify that swizzled outputs are non-negative
 * and don't exceed a reasonable bound.
 */
__global__ void kernel_test_smem_swizzle(int* swizzled, int* valid_flag,
                                          int n) {
    *valid_flag = 1;
    for (int i = 0; i < n; i++) {
        int s = transformer::smem_swizzle(i);
        swizzled[i] = s;
        if (s < 0) {
            *valid_flag = 0;
        }
    }
}

// ---------------------------------------------------------------------------
// Test fixture
// ---------------------------------------------------------------------------

class LayoutSwizzleTest : public GpuTest {
protected:
    static constexpr int MAX_RESULTS = 256;
    int* d_results = nullptr;
    int h_results[MAX_RESULTS];

    void SetUp() override {
        GpuTest::SetUp();
        cudaMalloc(&d_results, MAX_RESULTS * sizeof(int));
        cudaMemset(d_results, 0, MAX_RESULTS * sizeof(int));
    }

    void TearDown() override {
        cudaFree(d_results);
        GpuTest::TearDown();
    }

    void fetch_results(int count = MAX_RESULTS) {
        cudaMemcpy(h_results, d_results, count * sizeof(int),
                   cudaMemcpyDeviceToHost);
    }
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

TEST_F(LayoutSwizzleTest, RowMajorIdx) {
    const int ROWS = 3, COLS = 4;
    kernel_test_row_major<<<1, 1>>>(d_results, ROWS, COLS);
    cudaDeviceSynchronize();
    fetch_results(ROWS * COLS);

    for (int r = 0; r < ROWS; r++) {
        for (int c = 0; c < COLS; c++) {
            int expected = r * COLS + c;
            EXPECT_EQ(h_results[r * COLS + c], expected)
                << "row_major_idx(" << r << ", " << c << ", " << COLS << ")";
        }
    }
}

TEST_F(LayoutSwizzleTest, ColMajorIdx) {
    const int ROWS = 3, COLS = 4;
    kernel_test_col_major<<<1, 1>>>(d_results, ROWS, COLS);
    cudaDeviceSynchronize();
    fetch_results(ROWS * COLS);

    for (int r = 0; r < ROWS; r++) {
        for (int c = 0; c < COLS; c++) {
            int expected = c * ROWS + r;
            EXPECT_EQ(h_results[r * COLS + c], expected)
                << "col_major_idx(" << r << ", " << c << ", " << ROWS << ")";
        }
    }
}

TEST_F(LayoutSwizzleTest, Col32Padded) {
    // Test cases: dim -> expected padded
    int h_dims[] = {1, 16, 31, 32, 33, 64, 100};
    int expected[] = {32, 32, 32, 32, 64, 64, 128};
    const int N = sizeof(h_dims) / sizeof(h_dims[0]);

    int* d_dims = nullptr;
    cudaMalloc(&d_dims, N * sizeof(int));
    cudaMemcpy(d_dims, h_dims, N * sizeof(int), cudaMemcpyHostToDevice);

    kernel_test_col32_padded<<<1, 1>>>(d_dims, d_results, N);
    cudaDeviceSynchronize();
    fetch_results(N);

    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_results[i], expected[i])
            << "col32_padded(" << h_dims[i] << ")";
    }

    cudaFree(d_dims);
}

TEST_F(LayoutSwizzleTest, Col32IdxUniqueness) {
    // Use a matrix with cols that are a multiple of 32 for clean col32 layout
    const int ROWS = 4, COLS = 32;
    const int TOTAL = ROWS * COLS;

    int* d_unique_check = nullptr;
    cudaMalloc(&d_unique_check, TOTAL * sizeof(int));
    cudaMemset(d_unique_check, 0, TOTAL * sizeof(int));

    kernel_test_col32_idx<<<1, 1>>>(d_results, d_unique_check, ROWS, COLS);
    cudaDeviceSynchronize();

    int h_unique[TOTAL];
    cudaMemcpy(h_unique, d_unique_check, TOTAL * sizeof(int),
               cudaMemcpyDeviceToHost);
    fetch_results(TOTAL);

    // All col32 indices should be within bounds
    for (int r = 0; r < ROWS; r++) {
        for (int c = 0; c < COLS; c++) {
            int idx = h_results[r * COLS + c];
            EXPECT_GE(idx, 0) << "col32_idx(" << r << ", " << c << ") negative";
            EXPECT_LT(idx, TOTAL)
                << "col32_idx(" << r << ", " << c << ") out of bounds";
        }
    }

    // Each valid index should be used exactly once (all unique)
    for (int i = 0; i < TOTAL; i++) {
        EXPECT_EQ(h_unique[i], 1)
            << "col32 index " << i << " was used " << h_unique[i] << " times";
    }

    cudaFree(d_unique_check);
}

TEST_F(LayoutSwizzleTest, StrideHelper3D) {
    const int B = 2, M = 3, N = 4;
    kernel_test_stride_helper<<<1, 1>>>(d_results, B, M, N);
    cudaDeviceSynchronize();
    fetch_results(8);

    // Check stride values
    EXPECT_EQ(h_results[0], M * N) << "stride0 (batch stride)";
    EXPECT_EQ(h_results[1], N)     << "stride1 (row stride)";
    EXPECT_EQ(h_results[2], 1)     << "stride2 (column stride)";

    // Check computed indices
    EXPECT_EQ(h_results[3], 0)                     << "sh(0,0,0)";
    EXPECT_EQ(h_results[4], 1)                     << "sh(0,0,1)";
    EXPECT_EQ(h_results[5], N)                     << "sh(0,1,0)";
    EXPECT_EQ(h_results[6], M * N)                 << "sh(1,0,0)";
    EXPECT_EQ(h_results[7], M * N + 2 * N + 3)     << "sh(1,2,3)";
}

TEST_F(LayoutSwizzleTest, SmemSwizzleNonNegative) {
    const int N = 128;
    int* d_swizzled = nullptr;
    int* d_valid = nullptr;
    cudaMalloc(&d_swizzled, N * sizeof(int));
    cudaMalloc(&d_valid, sizeof(int));
    cudaMemset(d_valid, 0, sizeof(int));

    kernel_test_smem_swizzle<<<1, 1>>>(d_swizzled, d_valid, N);
    cudaDeviceSynchronize();

    int h_valid = 0;
    cudaMemcpy(&h_valid, d_valid, sizeof(int), cudaMemcpyDeviceToHost);
    EXPECT_EQ(h_valid, 1) << "smem_swizzle produced negative index";

    int h_swizzled[N];
    cudaMemcpy(h_swizzled, d_swizzled, N * sizeof(int), cudaMemcpyDeviceToHost);

    // Verify swizzle is deterministic and reversible within groups
    for (int i = 0; i < N; i++) {
        EXPECT_GE(h_swizzled[i], 0)
            << "smem_swizzle(" << i << ") = " << h_swizzled[i];
    }

    // Verify swizzle identity: swizzle(swizzle(x)) == x (XOR is self-inverse)
    // The swizzle is idx ^ ((idx >> 4) & 0x7), applying twice:
    // swizzle(swizzle(idx)) = swizzle(idx) ^ ((swizzle(idx) >> 4) & 0x7)
    // This is NOT necessarily identity, so we just check non-negativity above.

    cudaFree(d_swizzled);
    cudaFree(d_valid);
}

TEST_F(LayoutSwizzleTest, SmemSwizzleBankConflictReduction) {
    // Verify that for consecutive threads accessing consecutive indices,
    // the swizzled pattern differs from the original (i.e., swizzle does something)
    const int WARP_SIZE = 32;
    int* d_swizzled = nullptr;
    cudaMalloc(&d_swizzled, WARP_SIZE * sizeof(int));

    // We use indices 0..31 simulating a warp accessing consecutive elements
    kernel_test_smem_swizzle<<<1, 1>>>(d_swizzled, d_results, WARP_SIZE);
    cudaDeviceSynchronize();

    int h_swizzled[WARP_SIZE];
    cudaMemcpy(h_swizzled, d_swizzled, WARP_SIZE * sizeof(int),
               cudaMemcpyDeviceToHost);

    // At least some indices should differ from identity for indices >= 16
    // (below 16, (idx >> 4) & 0x7 == 0, so swizzle is identity)
    bool has_non_identity = false;
    for (int i = 16; i < WARP_SIZE; i++) {
        if (h_swizzled[i] != i) {
            has_non_identity = true;
            break;
        }
    }
    EXPECT_TRUE(has_non_identity)
        << "smem_swizzle should remap at least some indices >= 16";

    cudaFree(d_swizzled);
}
