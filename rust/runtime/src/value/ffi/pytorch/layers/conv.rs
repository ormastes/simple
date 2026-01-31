//! 3D Convolutional layer for neural networks
//!
//! Provides Conv3D layer with Xavier initialization and forward pass.

use crate::value::RuntimeValue;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Mutex;

#[cfg(feature = "pytorch")]
use super::super::storage::{get_tensor, store_tensor, value_to_tensor_handle};

#[cfg(feature = "pytorch")]
use tch::{Device, Kind, Tensor};

// Macro to reduce feature flag duplication
macro_rules! pytorch_fn {
    ($name:ident, $params:tt, $body:block) => {
        #[cfg(feature = "pytorch")]
        #[no_mangle]
        pub extern "C" fn $name $params -> RuntimeValue $body

        #[cfg(not(feature = "pytorch"))]
        #[no_mangle]
        pub extern "C" fn $name $params -> RuntimeValue {
            RuntimeValue::NIL
        }
    };
}

// ============================================================================
// Conv3D Layer Storage
// ============================================================================

/// Conv3d layer: stores weight, bias, and config
#[cfg(feature = "pytorch")]
#[derive(Clone)]
struct Conv3dLayer {
    weight: i64,       // Tensor handle for weight [out_channels, in_channels, kD, kH, kW]
    bias: Option<i64>, // Tensor handle for bias [out_channels]
    stride: i64,
    padding: i64,
    dilation: i64,
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref CONV3D_MAP: Mutex<HashMap<i64, Conv3dLayer>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static CONV3D_COUNTER: AtomicI64 = AtomicI64::new(1);

#[cfg(feature = "pytorch")]
fn store_conv3d_layer(layer: Conv3dLayer) -> i64 {
    let handle = CONV3D_COUNTER.fetch_add(1, Ordering::SeqCst);
    CONV3D_MAP.lock().unwrap().insert(handle, layer);
    handle
}

#[cfg(feature = "pytorch")]
fn get_conv3d_layer(handle: i64) -> Option<Conv3dLayer> {
    CONV3D_MAP.lock().unwrap().get(&handle).cloned()
}

// ============================================================================
// Conv3D Operations
// ============================================================================

pytorch_fn!(rt_torch_conv3d_new, (in_channels: i64, out_channels: i64, kernel_size: i64), {
    // Create Conv3d layer with Xavier-initialized weights
    // Weight shape: [out_channels, in_channels, kD, kH, kW]
    let weight = Tensor::randn(
        &[out_channels, in_channels, kernel_size, kernel_size, kernel_size],
        (Kind::Float, Device::Cpu),
    );
    // Xavier initialization
    let fan_in = in_channels * kernel_size * kernel_size * kernel_size;
    let std_dev = (2.0 / fan_in as f64).sqrt();
    let weight = weight * std_dev;
    let weight_handle = store_tensor(weight);

    // Bias shape: [out_channels]
    let bias = Tensor::zeros(&[out_channels], (Kind::Float, Device::Cpu));
    let bias_handle = store_tensor(bias);

    let layer = Conv3dLayer {
        weight: weight_handle,
        bias: Some(bias_handle),
        stride: 1,
        padding: 0,
        dilation: 1,
    };

    let handle = store_conv3d_layer(layer);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_conv3d_forward, (layer: RuntimeValue, input: RuntimeValue), {
    let layer_handle = match layer.as_int() {
        Ok(h) => h,
        Err(_) => return RuntimeValue::NIL,
    };

    let conv_layer = match get_conv3d_layer(layer_handle) {
        Some(l) => l,
        None => return RuntimeValue::NIL,
    };

    let input_handle = match value_to_tensor_handle(input) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let input_tensor = match get_tensor(input_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let weight = match get_tensor(conv_layer.weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let bias = conv_layer.bias.and_then(get_tensor);

    let result = input_tensor.conv3d(
        &weight,
        bias.as_ref(),
        &[conv_layer.stride, conv_layer.stride, conv_layer.stride],
        &[conv_layer.padding, conv_layer.padding, conv_layer.padding],
        &[conv_layer.dilation, conv_layer.dilation, conv_layer.dilation],
        1, // groups
    );

    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(feature = "pytorch")]
    fn test_conv3d_new() {
        use super::*;
        let layer = rt_torch_conv3d_new(3, 16, 3);
        assert!(layer.is_int());
    }

    #[test]
    #[cfg(feature = "pytorch")]
    fn test_conv3d_forward() {
        use super::*;
        // Basic smoke test - would need actual tensors for full test
        let result = rt_torch_conv3d_forward(RuntimeValue::NIL, RuntimeValue::NIL);
        assert_eq!(result, RuntimeValue::NIL);
    }
}
