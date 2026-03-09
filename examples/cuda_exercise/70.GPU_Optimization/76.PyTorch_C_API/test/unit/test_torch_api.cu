/**
 * @file test_torch_api.cu
 * @brief Unit tests for the C API functions (matmul, linear forward/backward, attention)
 *
 * Tests validate input checking, numerical correctness against naive CPU
 * implementations, and proper error reporting through TorchStatus codes.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "torch_api.h"
#include <cuda_runtime.h>
#include <vector>
#include <random>
#include <cmath>

/**
 * @brief Test fixture that manages CUDA device memory for tensor descriptors
 */
class TorchAPITest : public ::testing::Test {
protected:
    std::mt19937 gen{42};

    /// Allocate a device tensor and fill with random values in [-1, 1]
    struct DeviceTensor {
        float* d_data = nullptr;
        std::vector<int64_t> shape;
        int64_t numel = 0;
        TorchTensorDesc desc{};

        ~DeviceTensor() {
            if (d_data) cudaFree(d_data);
        }
    };

    /// Create a device tensor with given shape, filled with random floats
    std::unique_ptr<DeviceTensor> makeTensor(std::initializer_list<int64_t> dims) {
        auto t = std::make_unique<DeviceTensor>();
        t->shape.assign(dims);
        t->numel = 1;
        for (auto d : t->shape) t->numel *= d;

        std::uniform_real_distribution<float> dist(-1.0f, 1.0f);
        std::vector<float> h_data(t->numel);
        for (auto& v : h_data) v = dist(gen);

        cudaMalloc(&t->d_data, sizeof(float) * t->numel);
        cudaMemcpy(t->d_data, h_data.data(), sizeof(float) * t->numel,
                   cudaMemcpyHostToDevice);

        t->desc.data = t->d_data;
        t->desc.shape = t->shape.data();
        t->desc.ndim = static_cast<int>(t->shape.size());
        t->desc.numel = t->numel;
        return t;
    }

    /// Create a zero-filled device tensor
    std::unique_ptr<DeviceTensor> makeZeroTensor(std::initializer_list<int64_t> dims) {
        auto t = std::make_unique<DeviceTensor>();
        t->shape.assign(dims);
        t->numel = 1;
        for (auto d : t->shape) t->numel *= d;

        cudaMalloc(&t->d_data, sizeof(float) * t->numel);
        cudaMemset(t->d_data, 0, sizeof(float) * t->numel);

        t->desc.data = t->d_data;
        t->desc.shape = t->shape.data();
        t->desc.ndim = static_cast<int>(t->shape.size());
        t->desc.numel = t->numel;
        return t;
    }

    /// Download device tensor to host vector
    std::vector<float> toHost(const DeviceTensor& t) {
        std::vector<float> h(t.numel);
        cudaMemcpy(h.data(), t.d_data, sizeof(float) * t.numel,
                   cudaMemcpyDeviceToHost);
        return h;
    }

    /// Naive CPU matmul for reference
    std::vector<float> cpuMatmul(const std::vector<float>& A,
                                  const std::vector<float>& B,
                                  int M, int N, int K) {
        std::vector<float> C(M * N, 0.0f);
        for (int i = 0; i < M; ++i)
            for (int j = 0; j < N; ++j)
                for (int k = 0; k < K; ++k)
                    C[i * N + j] += A[i * K + k] * B[k * N + j];
        return C;
    }
};

// ---- torch_matmul tests ----

TEST_F(TorchAPITest, MatmulNullDescriptor) {
    auto A = makeTensor({4, 8});
    auto B = makeTensor({8, 6});
    auto C = makeZeroTensor({4, 6});

    TorchStatus s = torch_matmul(nullptr, &A->desc, &B->desc);
    EXPECT_EQ(s, TORCH_ERROR_INVALID_ARGUMENT);

    s = torch_matmul(&C->desc, nullptr, &B->desc);
    EXPECT_EQ(s, TORCH_ERROR_INVALID_ARGUMENT);
}

TEST_F(TorchAPITest, MatmulDimensionMismatch) {
    auto A = makeTensor({4, 8});
    auto B = makeTensor({5, 6});  // K mismatch: 8 != 5
    auto C = makeZeroTensor({4, 6});

    TorchStatus s = torch_matmul(&C->desc, &A->desc, &B->desc);
    EXPECT_EQ(s, TORCH_ERROR_INVALID_ARGUMENT);
}

TEST_F(TorchAPITest, MatmulSmall) {
    const int M = 4, K = 8, N = 6;
    auto A = makeTensor({M, K});
    auto B = makeTensor({K, N});
    auto C = makeZeroTensor({M, N});

    TorchStatus s = torch_matmul(&C->desc, &A->desc, &B->desc);
    ASSERT_EQ(s, TORCH_SUCCESS);

    auto hA = toHost(*A);
    auto hB = toHost(*B);
    auto hC = toHost(*C);
    auto ref = cpuMatmul(hA, hB, M, N, K);

    for (int i = 0; i < M * N; ++i) {
        EXPECT_NEAR(hC[i], ref[i], 1e-3f) << "Mismatch at index " << i;
    }
}

TEST_F(TorchAPITest, MatmulLargerThanTile) {
    const int M = 65, K = 33, N = 70;
    auto A = makeTensor({M, K});
    auto B = makeTensor({K, N});
    auto C = makeZeroTensor({M, N});

    TorchStatus s = torch_matmul(&C->desc, &A->desc, &B->desc);
    ASSERT_EQ(s, TORCH_SUCCESS);

    auto hA = toHost(*A);
    auto hB = toHost(*B);
    auto hC = toHost(*C);
    auto ref = cpuMatmul(hA, hB, M, N, K);

    for (int i = 0; i < M * N; ++i) {
        EXPECT_NEAR(hC[i], ref[i], 1e-2f) << "Mismatch at index " << i;
    }
}

TEST_F(TorchAPITest, MatmulSquare) {
    const int N = 32;
    auto A = makeTensor({N, N});
    auto B = makeTensor({N, N});
    auto C = makeZeroTensor({N, N});

    TorchStatus s = torch_matmul(&C->desc, &A->desc, &B->desc);
    ASSERT_EQ(s, TORCH_SUCCESS);

    auto hA = toHost(*A);
    auto hB = toHost(*B);
    auto hC = toHost(*C);
    auto ref = cpuMatmul(hA, hB, N, N, N);

    for (int i = 0; i < N * N; ++i) {
        EXPECT_NEAR(hC[i], ref[i], 1e-3f);
    }
}

// ---- torch_linear_forward tests ----

TEST_F(TorchAPITest, LinearForwardCorrectness) {
    const int batch = 4, in_f = 8, out_f = 6;
    auto input = makeTensor({batch, in_f});
    auto weight = makeTensor({out_f, in_f});
    auto bias = makeTensor({1, out_f});  // 2-D for descriptor compatibility
    auto output = makeZeroTensor({batch, out_f});

    TorchStatus s = torch_linear_forward(&output->desc, &input->desc,
                                          &weight->desc, &bias->desc);
    ASSERT_EQ(s, TORCH_SUCCESS);

    // Reference: output = input * weight^T + bias
    auto hIn = toHost(*input);
    auto hW = toHost(*weight);
    auto hB = toHost(*bias);
    auto hOut = toHost(*output);

    for (int i = 0; i < batch; ++i) {
        for (int j = 0; j < out_f; ++j) {
            float expected = hB[j];
            for (int k = 0; k < in_f; ++k) {
                expected += hIn[i * in_f + k] * hW[j * in_f + k];
            }
            EXPECT_NEAR(hOut[i * out_f + j], expected, 1e-2f)
                << "Mismatch at [" << i << "," << j << "]";
        }
    }
}

TEST_F(TorchAPITest, LinearForwardNoBias) {
    const int batch = 4, in_f = 8, out_f = 6;
    auto input = makeTensor({batch, in_f});
    auto weight = makeTensor({out_f, in_f});
    auto output = makeZeroTensor({batch, out_f});

    TorchStatus s = torch_linear_forward(&output->desc, &input->desc,
                                          &weight->desc, nullptr);
    ASSERT_EQ(s, TORCH_SUCCESS);

    auto hIn = toHost(*input);
    auto hW = toHost(*weight);
    auto hOut = toHost(*output);

    for (int i = 0; i < batch; ++i) {
        for (int j = 0; j < out_f; ++j) {
            float expected = 0.0f;
            for (int k = 0; k < in_f; ++k) {
                expected += hIn[i * in_f + k] * hW[j * in_f + k];
            }
            EXPECT_NEAR(hOut[i * out_f + j], expected, 1e-2f);
        }
    }
}

// ---- torch_scaled_dot_product_attention tests ----

TEST_F(TorchAPITest, AttentionNoCausal) {
    const int seq = 4, dim = 8;
    auto Q = makeTensor({seq, dim});
    auto K = makeTensor({seq, dim});
    auto V = makeTensor({seq, dim});
    auto out = makeZeroTensor({seq, dim});

    TorchStatus s = torch_scaled_dot_product_attention(
            &out->desc, &Q->desc, &K->desc, &V->desc, 0);
    ASSERT_EQ(s, TORCH_SUCCESS);

    // Verify output is non-zero (smoke test)
    auto hOut = toHost(*out);
    float sum = 0.0f;
    for (auto v : hOut) sum += std::abs(v);
    EXPECT_GT(sum, 0.0f);
}

TEST_F(TorchAPITest, AttentionCausal) {
    const int seq = 4, dim = 8;
    auto Q = makeTensor({seq, dim});
    auto K = makeTensor({seq, dim});
    auto V = makeTensor({seq, dim});
    auto out = makeZeroTensor({seq, dim});

    TorchStatus s = torch_scaled_dot_product_attention(
            &out->desc, &Q->desc, &K->desc, &V->desc, 1);
    ASSERT_EQ(s, TORCH_SUCCESS);

    auto hOut = toHost(*out);
    float sum = 0.0f;
    for (auto v : hOut) sum += std::abs(v);
    EXPECT_GT(sum, 0.0f);
}

TEST_F(TorchAPITest, AttentionIdentityValues) {
    // When V is identity-like, attention output should be weighted combination of rows
    const int seq = 4, dim = 4;
    auto Q = makeZeroTensor({seq, dim});
    auto K = makeZeroTensor({seq, dim});

    // V = identity
    std::vector<float> v_data(seq * dim, 0.0f);
    for (int i = 0; i < std::min(seq, dim); ++i) v_data[i * dim + i] = 1.0f;

    auto V = std::make_unique<DeviceTensor>();
    V->shape = {seq, dim};
    V->numel = seq * dim;
    cudaMalloc(&V->d_data, sizeof(float) * V->numel);
    cudaMemcpy(V->d_data, v_data.data(), sizeof(float) * V->numel,
               cudaMemcpyHostToDevice);
    V->desc.data = V->d_data;
    V->desc.shape = V->shape.data();
    V->desc.ndim = 2;
    V->desc.numel = V->numel;

    auto out = makeZeroTensor({seq, dim});

    TorchStatus s = torch_scaled_dot_product_attention(
            &out->desc, &Q->desc, &K->desc, &V->desc, 0);
    ASSERT_EQ(s, TORCH_SUCCESS);

    // With Q=K=0, scores are all 0, softmax gives uniform weights 1/seq
    // output[i] = (1/seq) * sum of V rows
    auto hOut = toHost(*out);
    float expected_per_col = 1.0f / seq;
    for (int i = 0; i < seq; ++i) {
        for (int j = 0; j < dim; ++j) {
            EXPECT_NEAR(hOut[i * dim + j], expected_per_col, 1e-3f)
                << "At [" << i << "," << j << "]";
        }
    }
}
