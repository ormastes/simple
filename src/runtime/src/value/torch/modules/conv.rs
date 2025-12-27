//! Convolutional Layers and Pooling Operations
//!
//! Provides:
//! - Conv2d layer
//! - Max and average pooling (2D)
//! - Global pooling (average and max)
//! - Adaptive pooling

#[cfg(feature = "pytorch")]
use super::{ModuleState, MODULE_REGISTRY, next_module_handle};

#[cfg(feature = "pytorch")]
use super::{TENSOR_REGISTRY, TensorWrapper, next_handle};

#[cfg(feature = "pytorch")]
use super::{rt_torch_randn, rt_torch_zeros, rt_torch_free, rt_torch_set_requires_grad,
            rt_torch_kaiming_uniform_};

#[cfg(feature = "pytorch")]
use tch::Kind as TchKind;

/// Create a Conv2d layer
/// in_channels, out_channels: channel counts
/// kernel_size: size of convolution kernel (square)
/// stride: stride of convolution
/// padding: zero padding added to both sides
#[no_mangle]
pub extern "C" fn rt_torch_conv2d_new(
    in_channels: i64,
    out_channels: i64,
    kernel_size: i64,
    stride: i64,
    padding: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if in_channels <= 0 || out_channels <= 0 || kernel_size <= 0 || stride <= 0 || padding < 0
        {
            return 0;
        }

        // Weight shape: [out_channels, in_channels, kernel_size, kernel_size]
        let weight_shape = vec![out_channels, in_channels, kernel_size, kernel_size];
        let weight_handle = rt_torch_randn(weight_shape.as_ptr(), 4, 0, 0);
        if weight_handle == 0 {
            return 0;
        }

        // Apply Kaiming initialization
        let _ = rt_torch_kaiming_uniform_(weight_handle, 5.0_f64.sqrt());

        let weight_with_grad = rt_torch_set_requires_grad(weight_handle, 1);
        rt_torch_free(weight_handle);

        // Bias: [out_channels]
        let bias_shape = vec![out_channels];
        let bias = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);
        if bias == 0 {
            rt_torch_free(weight_with_grad);
            return 0;
        }
        let bias_with_grad = rt_torch_set_requires_grad(bias, 1);
        rt_torch_free(bias);

        let state = ModuleState::Conv2d {
            weight: weight_with_grad,
            bias: Some(bias_with_grad),
            stride: (stride, stride),
            padding: (padding, padding),
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, std::sync::Arc::new(state));

        tracing::debug!(
            "rt_torch_conv2d_new: handle={} in_ch={} out_ch={} kernel={} stride={} padding={}",
            handle,
            in_channels,
            out_channels,
            kernel_size,
            stride,
            padding
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (in_channels, out_channels, kernel_size, stride, padding);
        0
    }
}

/// Forward pass through Conv2d layer
#[no_mangle]
pub extern "C" fn rt_torch_conv2d_forward(module_handle: u64, input_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle).cloned() else {
            return 0;
        };
        drop(module_registry);

        match module.as_ref() {
            ModuleState::Conv2d {
                weight,
                bias,
                stride,
                padding,
            } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(input) = tensor_registry.get(&input_handle).cloned() else {
                    return 0;
                };
                let Some(w) = tensor_registry.get(weight).cloned() else {
                    return 0;
                };
                let bias_tensor = bias.and_then(|b| tensor_registry.get(&b).cloned());
                drop(tensor_registry);

                // Perform 2D convolution
                let result = input.0.conv2d(
                    &w.0,
                    bias_tensor.as_ref().map(|b| &b.0),
                    &[stride.0, stride.1],
                    &[padding.0, padding.1],
                    &[1, 1],  // dilation
                    1,         // groups
                );

                let handle = next_handle();
                TENSOR_REGISTRY
                    .lock()
                    .insert(handle, std::sync::Arc::new(TensorWrapper(result)));

                tracing::debug!(
                    "rt_torch_conv2d_forward: module={} input={} -> output={}",
                    module_handle,
                    input_handle,
                    handle
                );
                handle
            }
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (module_handle, input_handle);
        0
    }
}

/// Max pooling 2D
#[no_mangle]
pub extern "C" fn rt_torch_max_pool2d(
    input_handle: u64,
    kernel_size: i64,
    stride: i64,
    padding: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(input) = tensor_registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(tensor_registry);

        let result = input.0.max_pool2d(
            &[kernel_size, kernel_size],
            &[stride, stride],
            &[padding, padding],
            &[1, 1],
            false,
        );

        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, std::sync::Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_max_pool2d: input={} kernel={} stride={} padding={} -> {}",
            input_handle,
            kernel_size,
            stride,
            padding,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, kernel_size, stride, padding);
        0
    }
}

/// Average pooling 2D
#[no_mangle]
pub extern "C" fn rt_torch_avg_pool2d(
    input_handle: u64,
    kernel_size: i64,
    stride: i64,
    padding: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(input) = tensor_registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(tensor_registry);

        let result = input.0.avg_pool2d(
            &[kernel_size, kernel_size],
            &[stride, stride],
            &[padding, padding],
            false,
            true,
            None,
        );

        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, std::sync::Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_avg_pool2d: input={} kernel={} stride={} padding={} -> {}",
            input_handle,
            kernel_size,
            stride,
            padding,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, kernel_size, stride, padding);
        0
    }
}

// ============================================================================
// Global & Adaptive Pooling
// ============================================================================

/// Global Average Pooling 2D - reduces spatial dimensions to 1x1
/// Input: [N, C, H, W] -> Output: [N, C, 1, 1]
#[no_mangle]
pub extern "C" fn rt_torch_global_avg_pool2d(input_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(registry);

        // Global average pooling: mean over spatial dimensions (H, W)
        let result = input.0.mean_dim(Some(&[2i64, 3][..]), true, TchKind::Float);

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, std::sync::Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_global_avg_pool2d: input={} -> {}",
            input_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = input_handle;
        0
    }
}

/// Global Max Pooling 2D - reduces spatial dimensions to 1x1
/// Input: [N, C, H, W] -> Output: [N, C, 1, 1]
#[no_mangle]
pub extern "C" fn rt_torch_global_max_pool2d(input_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(registry);

        // Global max pooling: max over spatial dimensions (H, W)
        // First max over H (dim 2), then max over W (dim 3)
        let max_h = input.0.max_dim(2, true).0;
        let result = max_h.max_dim(3, true).0;

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, std::sync::Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_global_max_pool2d: input={} -> {}",
            input_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = input_handle;
        0
    }
}

/// Adaptive Average Pooling 2D - pools to target output size
/// Input: [N, C, H, W] -> Output: [N, C, output_h, output_w]
#[no_mangle]
pub extern "C" fn rt_torch_adaptive_avg_pool2d(
    input_handle: u64,
    output_h: i64,
    output_w: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(registry);

        if output_h <= 0 || output_w <= 0 {
            return 0;
        }

        // Adaptive average pooling to target size
        let result = input.0.adaptive_avg_pool2d(&[output_h, output_w]);

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, std::sync::Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_adaptive_avg_pool2d: input={} size=[{},{}] -> {}",
            input_handle,
            output_h,
            output_w,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, output_h, output_w);
        0
    }
}

/// Adaptive Max Pooling 2D - pools to target output size
/// Input: [N, C, H, W] -> Output: [N, C, output_h, output_w]
#[no_mangle]
pub extern "C" fn rt_torch_adaptive_max_pool2d(
    input_handle: u64,
    output_h: i64,
    output_w: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(registry);

        if output_h <= 0 || output_w <= 0 {
            return 0;
        }

        // Adaptive max pooling to target size
        // Returns (output, indices), we only need output
        let (result, _indices) = input.0.adaptive_max_pool2d(&[output_h, output_w]);

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, std::sync::Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_adaptive_max_pool2d: input={} size=[{},{}] -> {}",
            input_handle,
            output_h,
            output_w,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, output_h, output_w);
        0
    }
}
