/**
 * @file torch_backprop_api.cpp
 * @brief C API implementation for linear layer forward and backward passes
 *
 * Implements the forward pass (output = input * weight^T + bias) and the
 * backward pass that computes gradients for input, weight, and bias.
 * Both functions validate inputs and delegate to CUDA kernel launchers.
 */

#include "torch_api.h"
#include "matmul_kernel.h"
#include <cuda_runtime.h>
#include <cstdio>
#include <cstring>

/**
 * @brief Helper to validate a tensor descriptor (may be NULL for optional tensors)
 */
static TorchStatus validate_backprop_tensor(const TorchTensorDesc* desc,
                                            const char* name, bool optional) {
    if (!desc) {
        if (optional) return TORCH_SUCCESS;
        fprintf(stderr, "torch_linear: %s descriptor is NULL\n", name);
        return TORCH_ERROR_INVALID_ARGUMENT;
    }
    if (!desc->data && !optional) {
        fprintf(stderr, "torch_linear: %s data pointer is NULL\n", name);
        return TORCH_ERROR_INVALID_ARGUMENT;
    }
    return TORCH_SUCCESS;
}

extern "C" TorchStatus torch_linear_forward(TorchTensorDesc* output,
                                             const TorchTensorDesc* input,
                                             const TorchTensorDesc* weight,
                                             const TorchTensorDesc* bias) {
    // Validate required tensors
    TorchStatus s;
    s = validate_backprop_tensor(output, "output", false);
    if (s != TORCH_SUCCESS) return s;
    s = validate_backprop_tensor(input, "input", false);
    if (s != TORCH_SUCCESS) return s;
    s = validate_backprop_tensor(weight, "weight", false);
    if (s != TORCH_SUCCESS) return s;
    // bias is optional
    s = validate_backprop_tensor(bias, "bias", true);
    if (s != TORCH_SUCCESS) return s;

    // input: [batch x in_features]
    // weight: [out_features x in_features]  (we need weight^T for the multiply)
    // output: [batch x out_features]
    int batch = static_cast<int>(input->shape[0]);
    int in_features = static_cast<int>(input->shape[1]);
    int out_features = static_cast<int>(weight->shape[0]);

    if (static_cast<int>(weight->shape[1]) != in_features) {
        fprintf(stderr, "torch_linear_forward: weight in_features mismatch\n");
        return TORCH_ERROR_INVALID_ARGUMENT;
    }

    // Allocate temporary for weight^T on device
    float* weight_t = nullptr;
    cudaError_t err = cudaMalloc(&weight_t, sizeof(float) * in_features * out_features);
    if (err != cudaSuccess) {
        fprintf(stderr, "torch_linear_forward: cudaMalloc failed: %s\n",
                cudaGetErrorString(err));
        return TORCH_ERROR_OUT_OF_MEMORY;
    }

    // Transpose weight using matmul with identity is expensive; use a simple
    // kernel-free approach: treat weight as B^T by launching matmul(A, B^T).
    // For simplicity, we transpose on device with a small kernel or just
    // do: output = input * weight^T.
    // We reuse the matmul kernel with transposed indexing by doing:
    //   C[batch x out] = A[batch x in] * B^T  where B is [out x in].
    // This is equivalent to: C = A * B^T => for each (i,j), sum_k A[i,k]*B[j,k]
    // Our tiled_matmul assumes B is [K x N], so we need B^T [in x out].
    // Allocate and transpose.

    // Simple transpose kernel - launch inline
    // For now, do a synchronous transpose via the existing matmul infrastructure
    // by creating a transposed copy.
    {
        // Copy weight to host, transpose, copy back
        // Better: use a device transpose. For this module, we use a simple approach.
        float* w_host = new float[in_features * out_features];
        err = cudaMemcpy(w_host, weight->data, sizeof(float) * in_features * out_features,
                         cudaMemcpyDeviceToHost);
        if (err != cudaSuccess) {
            delete[] w_host;
            cudaFree(weight_t);
            return TORCH_ERROR_CUDA;
        }

        float* wt_host = new float[in_features * out_features];
        for (int i = 0; i < out_features; ++i) {
            for (int j = 0; j < in_features; ++j) {
                wt_host[j * out_features + i] = w_host[i * in_features + j];
            }
        }

        err = cudaMemcpy(weight_t, wt_host, sizeof(float) * in_features * out_features,
                         cudaMemcpyHostToDevice);
        delete[] w_host;
        delete[] wt_host;
        if (err != cudaSuccess) {
            cudaFree(weight_t);
            return TORCH_ERROR_CUDA;
        }
    }

    // output[batch x out_features] = input[batch x in_features] * weight_t[in_features x out_features]
    launch_tiled_matmul(output->data, input->data, weight_t, batch, out_features,
                        in_features, nullptr);

    cudaFree(weight_t);

    err = cudaGetLastError();
    if (err != cudaSuccess) {
        fprintf(stderr, "torch_linear_forward: CUDA error: %s\n", cudaGetErrorString(err));
        return TORCH_ERROR_CUDA;
    }

    // Add bias if provided
    if (bias && bias->data) {
        launch_add_bias(output->data, bias->data, batch, out_features, nullptr);
        err = cudaGetLastError();
        if (err != cudaSuccess) {
            fprintf(stderr, "torch_linear_forward: bias CUDA error: %s\n",
                    cudaGetErrorString(err));
            return TORCH_ERROR_CUDA;
        }
    }

    err = cudaDeviceSynchronize();
    if (err != cudaSuccess) return TORCH_ERROR_CUDA;

    return TORCH_SUCCESS;
}

extern "C" TorchStatus torch_linear_backward(TorchTensorDesc* grad_input,
                                              TorchTensorDesc* grad_weight,
                                              TorchTensorDesc* grad_bias,
                                              const TorchTensorDesc* grad_output,
                                              const TorchTensorDesc* input,
                                              const TorchTensorDesc* weight) {
    TorchStatus s;
    s = validate_backprop_tensor(grad_output, "grad_output", false);
    if (s != TORCH_SUCCESS) return s;
    s = validate_backprop_tensor(input, "input", false);
    if (s != TORCH_SUCCESS) return s;
    s = validate_backprop_tensor(weight, "weight", false);
    if (s != TORCH_SUCCESS) return s;
    s = validate_backprop_tensor(grad_input, "grad_input", false);
    if (s != TORCH_SUCCESS) return s;
    s = validate_backprop_tensor(grad_weight, "grad_weight", false);
    if (s != TORCH_SUCCESS) return s;

    int batch = static_cast<int>(input->shape[0]);
    int in_features = static_cast<int>(input->shape[1]);
    int out_features = static_cast<int>(weight->shape[0]);

    // grad_input[batch x in_features] = grad_output[batch x out_features] * weight[out_features x in_features]
    launch_tiled_matmul(grad_input->data, grad_output->data, weight->data,
                        batch, in_features, out_features, nullptr);

    cudaError_t err = cudaGetLastError();
    if (err != cudaSuccess) return TORCH_ERROR_CUDA;

    // grad_weight[out_features x in_features] = grad_output^T[out_features x batch] * input[batch x in_features]
    // We need grad_output transposed. Allocate and transpose.
    float* grad_out_t = nullptr;
    err = cudaMalloc(&grad_out_t, sizeof(float) * batch * out_features);
    if (err != cudaSuccess) return TORCH_ERROR_OUT_OF_MEMORY;

    {
        float* go_host = new float[batch * out_features];
        err = cudaMemcpy(go_host, grad_output->data, sizeof(float) * batch * out_features,
                         cudaMemcpyDeviceToHost);
        if (err != cudaSuccess) {
            delete[] go_host;
            cudaFree(grad_out_t);
            return TORCH_ERROR_CUDA;
        }

        float* got_host = new float[batch * out_features];
        for (int i = 0; i < batch; ++i) {
            for (int j = 0; j < out_features; ++j) {
                got_host[j * batch + i] = go_host[i * out_features + j];
            }
        }

        err = cudaMemcpy(grad_out_t, got_host, sizeof(float) * batch * out_features,
                         cudaMemcpyHostToDevice);
        delete[] go_host;
        delete[] got_host;
        if (err != cudaSuccess) {
            cudaFree(grad_out_t);
            return TORCH_ERROR_CUDA;
        }
    }

    // grad_weight[out x in] = grad_out_t[out x batch] * input[batch x in]
    launch_tiled_matmul(grad_weight->data, grad_out_t, input->data,
                        out_features, in_features, batch, nullptr);

    cudaFree(grad_out_t);

    err = cudaGetLastError();
    if (err != cudaSuccess) return TORCH_ERROR_CUDA;

    // grad_bias[out_features] = sum over batch of grad_output
    if (grad_bias && grad_bias->data) {
        launch_reduce_rows(grad_bias->data, grad_output->data, batch, out_features, nullptr);
        err = cudaGetLastError();
        if (err != cudaSuccess) return TORCH_ERROR_CUDA;
    }

    err = cudaDeviceSynchronize();
    if (err != cudaSuccess) return TORCH_ERROR_CUDA;

    return TORCH_SUCCESS;
}
