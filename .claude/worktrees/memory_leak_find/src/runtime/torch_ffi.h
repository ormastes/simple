/*
 * torch_ffi.h - C declarations for PyTorch SFFI bridge
 *
 * All rt_torch_* functions are implemented in torch_ffi.cpp and
 * exposed as a shared library (libspl_torch.so).
 */

#ifndef TORCH_FFI_H
#define TORCH_FFI_H

#include "runtime.h"
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Library information */
bool        rt_torch_available(void);
char*       rt_torch_version(void);
bool        rt_torch_cuda_available(void);

/* Tensor creation */
int64_t     rt_torch_tensor_zeros(SplArray* dims);
int64_t     rt_torch_tensor_ones(SplArray* dims);
int64_t     rt_torch_tensor_randn(SplArray* dims);
int64_t     rt_torch_tensor_rand(SplArray* dims);
int64_t     rt_torch_tensor_full(SplArray* dims, double value);
int64_t     rt_torch_tensor_from_data(SplArray* data, SplArray* dims);
int64_t     rt_torch_tensor_arange(double start, double end, double step);
int64_t     rt_torch_tensor_linspace(double start, double end, int64_t steps);
int64_t     rt_torch_tensor_eye(int64_t n);
int64_t     rt_torch_tensor_empty(SplArray* dims);

/* Element-wise arithmetic */
int64_t     rt_torch_torchtensor_add(int64_t handle, int64_t other);
int64_t     rt_torch_torchtensor_sub(int64_t handle, int64_t other);
int64_t     rt_torch_torchtensor_mul(int64_t handle, int64_t other);
int64_t     rt_torch_torchtensor_div(int64_t handle, int64_t other);
int64_t     rt_torch_torchtensor_pow(int64_t handle, double exponent);
int64_t     rt_torch_torchtensor_neg(int64_t handle);
int64_t     rt_torch_torchtensor_abs(int64_t handle);
int64_t     rt_torch_torchtensor_sqrt(int64_t handle);
int64_t     rt_torch_torchtensor_exp(int64_t handle);
int64_t     rt_torch_torchtensor_log(int64_t handle);
int64_t     rt_torch_torchtensor_add_scalar(int64_t handle, double scalar);
int64_t     rt_torch_torchtensor_mul_scalar(int64_t handle, double scalar);

/* Activation functions */
int64_t     rt_torch_torchtensor_relu(int64_t handle);
int64_t     rt_torch_torchtensor_sigmoid(int64_t handle);
int64_t     rt_torch_torchtensor_tanh(int64_t handle);
int64_t     rt_torch_torchtensor_leaky_relu(int64_t handle, double negative_slope);
int64_t     rt_torch_torchtensor_gelu(int64_t handle);
int64_t     rt_torch_torchtensor_softmax(int64_t handle, int64_t dim);
int64_t     rt_torch_torchtensor_log_softmax(int64_t handle, int64_t dim);

/* Linear algebra */
int64_t     rt_torch_torchtensor_matmul(int64_t handle, int64_t other);
int64_t     rt_torch_torchtensor_dot(int64_t handle, int64_t other);
int64_t     rt_torch_torchtensor_transpose(int64_t handle, int64_t dim0, int64_t dim1);
int64_t     rt_torch_torchtensor_t(int64_t handle);
double      rt_torch_torchtensor_norm(int64_t handle);
double      rt_torch_torchtensor_det(int64_t handle);
int64_t     rt_torch_torchtensor_inverse(int64_t handle);
int64_t     rt_torch_torchtensor_svd(int64_t handle);
int64_t     rt_torch_torchtensor_eig(int64_t handle);

/* Reductions */
double      rt_torch_torchtensor_sum(int64_t handle);
int64_t     rt_torch_torchtensor_sum_dim(int64_t handle, int64_t dim, bool keepdim);
double      rt_torch_torchtensor_mean(int64_t handle);
int64_t     rt_torch_torchtensor_mean_dim(int64_t handle, int64_t dim, bool keepdim);
double      rt_torch_torchtensor_max(int64_t handle);
int64_t     rt_torch_torchtensor_max_dim(int64_t handle, int64_t dim, bool keepdim);
double      rt_torch_torchtensor_min(int64_t handle);
int64_t     rt_torch_torchtensor_min_dim(int64_t handle, int64_t dim, bool keepdim);
int64_t     rt_torch_torchtensor_argmax(int64_t handle, int64_t dim, bool keepdim);
int64_t     rt_torch_torchtensor_argmin(int64_t handle, int64_t dim, bool keepdim);
double      rt_torch_torchtensor_std(int64_t handle);
double      rt_torch_torchtensor_var(int64_t handle);

/* Shape manipulation */
int64_t     rt_torch_torchtensor_ndim(int64_t handle);
int64_t     rt_torch_torchtensor_numel(int64_t handle);
SplArray*   rt_torch_torchtensor_shape(int64_t handle);
int64_t     rt_torch_torchtensor_reshape(int64_t handle, SplArray* dims);
int64_t     rt_torch_torchtensor_view(int64_t handle, SplArray* dims);
int64_t     rt_torch_torchtensor_permute(int64_t handle, SplArray* dims);
int64_t     rt_torch_torchtensor_squeeze(int64_t handle);
int64_t     rt_torch_torchtensor_squeeze_dim(int64_t handle, int64_t dim);
int64_t     rt_torch_torchtensor_unsqueeze(int64_t handle, int64_t dim);
int64_t     rt_torch_torchtensor_flatten(int64_t handle);
int64_t     rt_torch_torchtensor_contiguous(int64_t handle);

/* Indexing and slicing */
int64_t     rt_torch_torchtensor_slice(int64_t handle, int64_t dim, int64_t start, int64_t end, int64_t step);
int64_t     rt_torch_torchtensor_index_select(int64_t handle, int64_t dim, int64_t indices);
int64_t     rt_torch_torchtensor_gather(int64_t handle, int64_t dim, int64_t indices);
int64_t     rt_torch_torchtensor_cat(SplArray* tensors, int64_t dim);
int64_t     rt_torch_torchtensor_stack(SplArray* tensors, int64_t dim);
SplArray*   rt_torch_torchtensor_chunk(int64_t handle, int64_t chunks, int64_t dim);

/* Neural network operations */
int64_t     rt_torch_nn_conv2d(int64_t input, int64_t weight, int64_t bias, SplArray* stride, SplArray* padding, SplArray* dilation, int64_t groups);
int64_t     rt_torch_nn_max_pool2d(int64_t input, SplArray* kernel_size, SplArray* stride, SplArray* padding);
int64_t     rt_torch_nn_avg_pool2d(int64_t input, SplArray* kernel_size, SplArray* stride, SplArray* padding);
int64_t     rt_torch_nn_batch_norm(int64_t input, int64_t running_mean, int64_t running_var, int64_t weight, int64_t bias, bool training, double momentum, double eps);
int64_t     rt_torch_nn_layer_norm(int64_t input, SplArray* normalized_shape, int64_t weight, int64_t bias, double eps);
int64_t     rt_torch_nn_dropout(int64_t input, double p, bool training);
int64_t     rt_torch_nn_linear(int64_t input, int64_t weight, int64_t bias);
int64_t     rt_torch_nn_embedding(int64_t input, int64_t weight);

/* Loss functions */
double      rt_torch_nn_mse_loss(int64_t input, int64_t target);
double      rt_torch_nn_cross_entropy(int64_t input, int64_t target);
double      rt_torch_nn_binary_cross_entropy(int64_t input, int64_t target);
double      rt_torch_nn_nll_loss(int64_t input, int64_t target);

/* Autograd */
void        rt_torch_autograd_set_requires_grad(int64_t handle, bool requires_grad);
bool        rt_torch_autograd_requires_grad(int64_t handle);
int64_t     rt_torch_autograd_grad(int64_t handle);
void        rt_torch_autograd_backward(int64_t handle);
void        rt_torch_autograd_zero_grad(int64_t handle);
int64_t     rt_torch_autograd_detach(int64_t handle);
void        rt_torch_autograd_no_grad_begin(void);
void        rt_torch_autograd_no_grad_end(void);

/* Device management */
int64_t     rt_torch_torchtensor_cuda(int64_t handle, int32_t device_id);
int64_t     rt_torch_torchtensor_cpu(int64_t handle);
bool        rt_torch_torchtensor_is_cuda(int64_t handle);
int32_t     rt_torch_torchtensor_device(int64_t handle);
int64_t     rt_torch_torchtensor_to_stream(int64_t handle, int32_t device_id, int64_t stream);
int64_t     rt_torch_torchtensor_clone(int64_t handle);

/* CUDA streams */
int64_t     rt_torch_stream_create(int32_t device_id);
void        rt_torch_torchstream_sync(int64_t handle);
bool        rt_torch_torchstream_query(int64_t handle);
void        rt_torch_torchstream_free(int64_t handle);

/* Memory management */
void        rt_torch_torchtensor_free(int64_t handle);
int64_t     rt_torch_cuda_memory_allocated(int32_t device_id);
int64_t     rt_torch_cuda_max_memory_allocated(int32_t device_id);
void        rt_torch_cuda_empty_cache(void);

#ifdef __cplusplus
}
#endif

#endif /* TORCH_FFI_H */
