/**
 * @file test_cpu_backprop.cu
 * @brief Unit tests for CPU backpropagation
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cpu_backprop.h"
#include <vector>
#include <random>
#include <cmath>

/**
 * Test fixture for CPU Backprop tests
 */
class CPUBackpropTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Seed random number generator
        gen.seed(12345);
    }

    std::mt19937 gen;

    /// Helper: Generate random matrix
    std::vector<float> randomMatrix(int rows, int cols) {
        std::vector<float> mat(rows * cols);
        std::uniform_real_distribution<float> dist(-1.0f, 1.0f);
        for (auto& val : mat) {
            val = dist(gen);
        }
        return mat;
    }

    /// Helper: Generate random vector
    std::vector<float> randomVector(int size) {
        std::vector<float> vec(size);
        std::uniform_real_distribution<float> dist(-1.0f, 1.0f);
        for (auto& val : vec) {
            val = dist(gen);
        }
        return vec;
    }

    /// Helper: Reference forward pass
    std::vector<float> referenceForward(const float* input, const float* weights, const float* bias,
                                         int batch_size, int input_dim, int output_dim) {
        std::vector<float> output(batch_size * output_dim);
        for (int b = 0; b < batch_size; b++) {
            for (int o = 0; o < output_dim; o++) {
                float sum = bias[o];
                for (int i = 0; i < input_dim; i++) {
                    sum += input[b * input_dim + i] * weights[o * input_dim + i];
                }
                output[b * output_dim + o] = sum;
            }
        }
        return output;
    }

    /// Helper: Reference backward pass - grad_input
    std::vector<float> referenceGradInput(const float* grad_output, const float* weights,
                                           int batch_size, int input_dim, int output_dim) {
        std::vector<float> grad_input(batch_size * input_dim);
        for (int b = 0; b < batch_size; b++) {
            for (int i = 0; i < input_dim; i++) {
                float sum = 0.0f;
                for (int o = 0; o < output_dim; o++) {
                    sum += grad_output[b * output_dim + o] * weights[o * input_dim + i];
                }
                grad_input[b * input_dim + i] = sum;
            }
        }
        return grad_input;
    }

    /// Helper: Reference backward pass - grad_weights
    std::vector<float> referenceGradWeights(const float* grad_output, const float* input,
                                             int batch_size, int input_dim, int output_dim) {
        std::vector<float> grad_weights(output_dim * input_dim);
        for (int o = 0; o < output_dim; o++) {
            for (int i = 0; i < input_dim; i++) {
                float sum = 0.0f;
                for (int b = 0; b < batch_size; b++) {
                    sum += grad_output[b * output_dim + o] * input[b * input_dim + i];
                }
                grad_weights[o * input_dim + i] = sum;
            }
        }
        return grad_weights;
    }

    /// Helper: Reference backward pass - grad_bias
    std::vector<float> referenceGradBias(const float* grad_output,
                                          int batch_size, int output_dim) {
        std::vector<float> grad_bias(output_dim);
        for (int o = 0; o < output_dim; o++) {
            float sum = 0.0f;
            for (int b = 0; b < batch_size; b++) {
                sum += grad_output[b * output_dim + o];
            }
            grad_bias[o] = sum;
        }
        return grad_bias;
    }

    /// Helper: Compare arrays
    bool arraysEqual(const float* A, const float* B, int size, float tol = 1e-4f) {
        for (int i = 0; i < size; i++) {
            if (std::abs(A[i] - B[i]) > tol) {
                return false;
            }
        }
        return true;
    }
};

/**
 * Test forward pass correctness
 */
TEST_F(CPUBackpropTest, ForwardCorrectness) {
    const int batch_size = 32, input_dim = 64, output_dim = 32;

    auto input = randomMatrix(batch_size, input_dim);
    auto weights = randomMatrix(output_dim, input_dim);
    auto bias = randomVector(output_dim);
    std::vector<float> output(batch_size * output_dim);

    cpu_forward(output.data(), input.data(), weights.data(), bias.data(),
                batch_size, input_dim, output_dim);

    auto output_ref = referenceForward(input.data(), weights.data(), bias.data(),
                                        batch_size, input_dim, output_dim);

    EXPECT_TRUE(arraysEqual(output.data(), output_ref.data(), batch_size * output_dim));
}

/**
 * Test backward pass gradient correctness
 */
TEST_F(CPUBackpropTest, BackwardGradients) {
    const int batch_size = 32, input_dim = 64, output_dim = 32;

    auto input = randomMatrix(batch_size, input_dim);
    auto weights = randomMatrix(output_dim, input_dim);
    auto grad_output = randomMatrix(batch_size, output_dim);

    std::vector<float> grad_input(batch_size * input_dim);
    std::vector<float> grad_weights(output_dim * input_dim);
    std::vector<float> grad_bias(output_dim);

    cpu_backward(grad_input.data(), grad_weights.data(), grad_bias.data(),
                 grad_output.data(), input.data(), weights.data(),
                 batch_size, input_dim, output_dim);

    auto grad_input_ref = referenceGradInput(grad_output.data(), weights.data(),
                                              batch_size, input_dim, output_dim);
    auto grad_weights_ref = referenceGradWeights(grad_output.data(), input.data(),
                                                  batch_size, input_dim, output_dim);
    auto grad_bias_ref = referenceGradBias(grad_output.data(), batch_size, output_dim);

    EXPECT_TRUE(arraysEqual(grad_input.data(), grad_input_ref.data(), batch_size * input_dim))
        << "grad_input mismatch";
    EXPECT_TRUE(arraysEqual(grad_weights.data(), grad_weights_ref.data(), output_dim * input_dim))
        << "grad_weights mismatch";
    EXPECT_TRUE(arraysEqual(grad_bias.data(), grad_bias_ref.data(), output_dim))
        << "grad_bias mismatch";
}

/**
 * Test ReLU forward pass
 */
TEST_F(CPUBackpropTest, ReluForward) {
    const int n = 256;
    auto input = randomVector(n);
    std::vector<float> output(n);

    cpu_relu_forward(output.data(), input.data(), n);

    for (int i = 0; i < n; i++) {
        float expected = (input[i] > 0.0f) ? input[i] : 0.0f;
        EXPECT_FLOAT_EQ(output[i], expected) << "Mismatch at index " << i;
    }
}

/**
 * Test ReLU backward pass
 */
TEST_F(CPUBackpropTest, ReluBackward) {
    const int n = 256;
    auto input = randomVector(n);
    auto grad_output = randomVector(n);
    std::vector<float> grad_input(n);

    cpu_relu_backward(grad_input.data(), grad_output.data(), input.data(), n);

    for (int i = 0; i < n; i++) {
        float expected = (input[i] > 0.0f) ? grad_output[i] : 0.0f;
        EXPECT_FLOAT_EQ(grad_input[i], expected) << "Mismatch at index " << i;
    }
}

/**
 * Test Sigmoid forward pass
 */
TEST_F(CPUBackpropTest, SigmoidForward) {
    const int n = 256;
    auto input = randomVector(n);
    std::vector<float> output(n);

    cpu_sigmoid_forward(output.data(), input.data(), n);

    for (int i = 0; i < n; i++) {
        float expected = 1.0f / (1.0f + expf(-input[i]));
        EXPECT_NEAR(output[i], expected, 1e-6f) << "Mismatch at index " << i;
    }
}

/**
 * Test Sigmoid backward pass
 */
TEST_F(CPUBackpropTest, SigmoidBackward) {
    const int n = 256;
    auto input = randomVector(n);
    std::vector<float> sigmoid_output(n);
    std::vector<float> grad_output(n);
    std::vector<float> grad_input(n);

    // First compute sigmoid forward
    cpu_sigmoid_forward(sigmoid_output.data(), input.data(), n);

    // Generate random grad_output
    std::uniform_real_distribution<float> dist(-1.0f, 1.0f);
    for (auto& val : grad_output) {
        val = dist(gen);
    }

    cpu_sigmoid_backward(grad_input.data(), grad_output.data(), sigmoid_output.data(), n);

    for (int i = 0; i < n; i++) {
        float s = sigmoid_output[i];
        float expected = grad_output[i] * s * (1.0f - s);
        EXPECT_NEAR(grad_input[i], expected, 1e-6f) << "Mismatch at index " << i;
    }
}

/**
 * Test parallel forward pass correctness
 */
TEST_F(CPUBackpropTest, ParallelForward) {
    const int batch_size = 64, input_dim = 128, output_dim = 64;

    auto input = randomMatrix(batch_size, input_dim);
    auto weights = randomMatrix(output_dim, input_dim);
    auto bias = randomVector(output_dim);
    std::vector<float> output(batch_size * output_dim);

    cpu_forward_parallel(output.data(), input.data(), weights.data(), bias.data(),
                         batch_size, input_dim, output_dim, 4);

    auto output_ref = referenceForward(input.data(), weights.data(), bias.data(),
                                        batch_size, input_dim, output_dim);

    EXPECT_TRUE(arraysEqual(output.data(), output_ref.data(), batch_size * output_dim));
}

/**
 * Test non-square dimensions
 */
TEST_F(CPUBackpropTest, NonSquareDimensions) {
    const int batch_size = 16, input_dim = 128, output_dim = 32;

    auto input = randomMatrix(batch_size, input_dim);
    auto weights = randomMatrix(output_dim, input_dim);
    auto bias = randomVector(output_dim);
    std::vector<float> output(batch_size * output_dim);

    cpu_forward(output.data(), input.data(), weights.data(), bias.data(),
                batch_size, input_dim, output_dim);

    auto output_ref = referenceForward(input.data(), weights.data(), bias.data(),
                                        batch_size, input_dim, output_dim);

    EXPECT_TRUE(arraysEqual(output.data(), output_ref.data(), batch_size * output_dim));

    // Also test backward with non-square
    auto grad_output = randomMatrix(batch_size, output_dim);
    std::vector<float> grad_input(batch_size * input_dim);
    std::vector<float> grad_weights(output_dim * input_dim);
    std::vector<float> grad_bias(output_dim);

    cpu_backward(grad_input.data(), grad_weights.data(), grad_bias.data(),
                 grad_output.data(), input.data(), weights.data(),
                 batch_size, input_dim, output_dim);

    auto grad_input_ref = referenceGradInput(grad_output.data(), weights.data(),
                                              batch_size, input_dim, output_dim);

    EXPECT_TRUE(arraysEqual(grad_input.data(), grad_input_ref.data(), batch_size * input_dim));
}

/**
 * Parameterized test for various (batch_size, input_dim, output_dim) combinations
 */
class BackpropSizeTest : public CPUBackpropTest,
                          public ::testing::WithParamInterface<std::tuple<int, int, int>> {};

TEST_P(BackpropSizeTest, VariousSizes) {
    auto [batch_size, input_dim, output_dim] = GetParam();

    auto input = randomMatrix(batch_size, input_dim);
    auto weights = randomMatrix(output_dim, input_dim);
    auto bias = randomVector(output_dim);
    auto grad_output = randomMatrix(batch_size, output_dim);

    // Test forward
    std::vector<float> output(batch_size * output_dim);
    cpu_forward(output.data(), input.data(), weights.data(), bias.data(),
                batch_size, input_dim, output_dim);

    auto output_ref = referenceForward(input.data(), weights.data(), bias.data(),
                                        batch_size, input_dim, output_dim);
    EXPECT_TRUE(arraysEqual(output.data(), output_ref.data(), batch_size * output_dim))
        << "Forward mismatch for (" << batch_size << ", " << input_dim << ", " << output_dim << ")";

    // Test backward
    std::vector<float> grad_input(batch_size * input_dim);
    std::vector<float> grad_weights(output_dim * input_dim);
    std::vector<float> grad_bias(output_dim);

    cpu_backward(grad_input.data(), grad_weights.data(), grad_bias.data(),
                 grad_output.data(), input.data(), weights.data(),
                 batch_size, input_dim, output_dim);

    auto grad_input_ref = referenceGradInput(grad_output.data(), weights.data(),
                                              batch_size, input_dim, output_dim);
    auto grad_weights_ref = referenceGradWeights(grad_output.data(), input.data(),
                                                  batch_size, input_dim, output_dim);
    auto grad_bias_ref = referenceGradBias(grad_output.data(), batch_size, output_dim);

    EXPECT_TRUE(arraysEqual(grad_input.data(), grad_input_ref.data(), batch_size * input_dim))
        << "grad_input mismatch for (" << batch_size << ", " << input_dim << ", " << output_dim << ")";
    EXPECT_TRUE(arraysEqual(grad_weights.data(), grad_weights_ref.data(), output_dim * input_dim))
        << "grad_weights mismatch for (" << batch_size << ", " << input_dim << ", " << output_dim << ")";
    EXPECT_TRUE(arraysEqual(grad_bias.data(), grad_bias_ref.data(), output_dim))
        << "grad_bias mismatch for (" << batch_size << ", " << input_dim << ", " << output_dim << ")";
}

INSTANTIATE_TEST_SUITE_P(
    SizeVariations,
    BackpropSizeTest,
    ::testing::Values(
        std::make_tuple(8, 32, 16),
        std::make_tuple(16, 64, 32),
        std::make_tuple(32, 128, 64),
        std::make_tuple(64, 256, 128),
        std::make_tuple(128, 512, 256)
    )
);

/**
 * Performance benchmark test
 */
TEST_F(CPUBackpropTest, PerformanceBenchmark) {
    const int batch_size = 128, input_dim = 256, output_dim = 128;

    auto input = randomMatrix(batch_size, input_dim);
    auto weights = randomMatrix(output_dim, input_dim);
    auto bias = randomVector(output_dim);
    auto grad_output_data = randomMatrix(batch_size, output_dim);

    std::vector<float> output(batch_size * output_dim);
    std::vector<float> grad_input(batch_size * input_dim);
    std::vector<float> grad_weights(output_dim * input_dim);
    std::vector<float> grad_bias(output_dim);

    float time_ms = cpu_forward_backward_timed(
        output.data(), grad_input.data(), grad_weights.data(), grad_bias.data(),
        input.data(), weights.data(), bias.data(), grad_output_data.data(),
        batch_size, input_dim, output_dim, "naive");

    // Calculate GFLOPS
    // Forward: 2*B*I*O + B*O, Backward: 4*B*I*O + B*O
    double total_flops = 6.0 * batch_size * input_dim * output_dim + 2.0 * batch_size * output_dim;
    double gflops = (total_flops / (time_ms / 1000.0)) / 1e9;

    std::cout << "Layer: batch=" << batch_size << ", in=" << input_dim << ", out=" << output_dim << std::endl;
    std::cout << "Time: " << time_ms << " ms" << std::endl;
    std::cout << "Performance: " << gflops << " GFLOPS" << std::endl;

    // Sanity check: naive CPU backprop should achieve at least some performance
    EXPECT_GT(gflops, 0.1) << "Performance too low for naive CPU backprop";
}
