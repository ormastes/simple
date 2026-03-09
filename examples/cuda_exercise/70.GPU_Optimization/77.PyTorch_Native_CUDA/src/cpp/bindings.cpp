/**
 * @file bindings.cpp
 * @brief pybind11 bindings for native CUDA operations
 *
 * Registers the CUDA kernel wrappers as Python-callable functions via PyTorch's
 * C++ extension mechanism. Each binding accepts torch::Tensor arguments, extracts
 * device pointers and dimensions, calls the CUDA launcher, and returns the result
 * as a new tensor.
 */

#include <torch/extension.h>
#include "native_ops.h"

/**
 * @brief Matrix multiplication: C = A @ B
 *
 * @param A  Input tensor [M x K], float32, CUDA
 * @param B  Input tensor [K x N], float32, CUDA
 * @return   Output tensor [M x N]
 */
torch::Tensor matmul_cuda(torch::Tensor A, torch::Tensor B) {
    TORCH_CHECK(A.is_cuda(), "A must be a CUDA tensor");
    TORCH_CHECK(B.is_cuda(), "B must be a CUDA tensor");
    TORCH_CHECK(A.dim() == 2 && B.dim() == 2, "A and B must be 2-D");
    TORCH_CHECK(A.size(1) == B.size(0), "Inner dimensions must match");

    int M = A.size(0);
    int K = A.size(1);
    int N = B.size(1);

    auto C = torch::empty({M, N}, A.options());
    native_matmul(C.data_ptr<float>(), A.data_ptr<float>(), B.data_ptr<float>(),
                  M, N, K);
    return C;
}

/**
 * @brief Linear forward: output = input @ weight^T + bias
 *
 * @param input   [batch x in_features], float32, CUDA
 * @param weight  [out_features x in_features], float32, CUDA
 * @param bias    [out_features] or empty tensor for no bias
 * @return        [batch x out_features]
 */
torch::Tensor linear_forward_cuda(torch::Tensor input, torch::Tensor weight,
                                   torch::Tensor bias) {
    TORCH_CHECK(input.is_cuda() && weight.is_cuda(), "Tensors must be on CUDA");
    int batch = input.size(0);
    int in_f = input.size(1);
    int out_f = weight.size(0);

    auto output = torch::empty({batch, out_f}, input.options());
    const float* bias_ptr = bias.numel() > 0 ? bias.data_ptr<float>() : nullptr;

    native_linear_forward(output.data_ptr<float>(), input.data_ptr<float>(),
                          weight.data_ptr<float>(), bias_ptr, batch, in_f, out_f);
    return output;
}

/**
 * @brief Linear backward: compute grad_input, grad_weight, grad_bias
 *
 * @param grad_output  [batch x out_features]
 * @param input        [batch x in_features]
 * @param weight       [out_features x in_features]
 * @param has_bias     Whether to compute grad_bias
 * @return Tuple of (grad_input, grad_weight, grad_bias)
 */
std::vector<torch::Tensor> linear_backward_cuda(torch::Tensor grad_output,
                                                  torch::Tensor input,
                                                  torch::Tensor weight,
                                                  bool has_bias) {
    TORCH_CHECK(grad_output.is_cuda() && input.is_cuda() && weight.is_cuda(),
                "Tensors must be on CUDA");
    int batch = input.size(0);
    int in_f = input.size(1);
    int out_f = weight.size(0);

    auto grad_input = torch::empty_like(input);
    auto grad_weight = torch::empty_like(weight);

    float* gb_ptr = nullptr;
    torch::Tensor grad_bias;
    if (has_bias) {
        grad_bias = torch::empty({out_f}, input.options());
        gb_ptr = grad_bias.data_ptr<float>();
    }

    native_linear_backward(grad_input.data_ptr<float>(), grad_weight.data_ptr<float>(),
                            gb_ptr, grad_output.data_ptr<float>(),
                            input.data_ptr<float>(), weight.data_ptr<float>(),
                            batch, in_f, out_f);

    if (has_bias) {
        return {grad_input, grad_weight, grad_bias};
    }
    return {grad_input, grad_weight};
}

/**
 * @brief Scaled dot-product attention
 *
 * @param Q       [seq_len x head_dim]
 * @param K       [seq_len x head_dim]
 * @param V       [seq_len x head_dim]
 * @param causal  Whether to apply causal mask
 * @return        [seq_len x head_dim]
 */
torch::Tensor attention_cuda(torch::Tensor Q, torch::Tensor K, torch::Tensor V,
                              bool causal) {
    TORCH_CHECK(Q.is_cuda() && K.is_cuda() && V.is_cuda(), "Tensors must be on CUDA");
    TORCH_CHECK(Q.dim() == 2, "Q must be 2-D [seq_len x head_dim]");

    int seq_len = Q.size(0);
    int head_dim = Q.size(1);

    auto output = torch::empty_like(Q);
    native_attention(output.data_ptr<float>(), Q.data_ptr<float>(),
                     K.data_ptr<float>(), V.data_ptr<float>(),
                     seq_len, head_dim, causal);
    return output;
}

PYBIND11_MODULE(TORCH_EXTENSION_NAME, m) {
    m.doc() = "Native CUDA operations for PyTorch (Module 77)";
    m.def("matmul", &matmul_cuda, "Tiled CUDA matrix multiplication",
          py::arg("A"), py::arg("B"));
    m.def("linear_forward", &linear_forward_cuda, "Linear forward pass",
          py::arg("input"), py::arg("weight"), py::arg("bias"));
    m.def("linear_backward", &linear_backward_cuda, "Linear backward pass",
          py::arg("grad_output"), py::arg("input"), py::arg("weight"),
          py::arg("has_bias") = true);
    m.def("attention", &attention_cuda, "Scaled dot-product attention",
          py::arg("Q"), py::arg("K"), py::arg("V"), py::arg("causal") = false);
}
