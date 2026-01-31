//! Recurrent Neural Network (RNN) layer
//!
//! Provides RNN layer with tanh activation, Xavier initialization, and forward pass.

use crate::value::RuntimeValue;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Mutex;

#[cfg(feature = "pytorch")]
use super::super::storage::{get_tensor, store_tensor, store_tensor_list, value_to_tensor_handle};

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
// RNN Layer Storage
// ============================================================================

/// RNN layer: stores weights for input-hidden and hidden-hidden
#[cfg(feature = "pytorch")]
#[derive(Clone)]
struct RnnLayer {
    weight_ih: i64, // Tensor handle [hidden_size, input_size]
    weight_hh: i64, // Tensor handle [hidden_size, hidden_size]
    bias_ih: Option<i64>,
    bias_hh: Option<i64>,
    hidden_size: i64,
    num_layers: i64,
    batch_first: bool,
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref RNN_MAP: Mutex<HashMap<i64, RnnLayer>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static RNN_COUNTER: AtomicI64 = AtomicI64::new(1);

#[cfg(feature = "pytorch")]
fn store_rnn_layer(layer: RnnLayer) -> i64 {
    let handle = RNN_COUNTER.fetch_add(1, Ordering::SeqCst);
    RNN_MAP.lock().unwrap().insert(handle, layer);
    handle
}

#[cfg(feature = "pytorch")]
fn get_rnn_layer(handle: i64) -> Option<RnnLayer> {
    RNN_MAP.lock().unwrap().get(&handle).cloned()
}

// ============================================================================
// RNN Operations
// ============================================================================

pytorch_fn!(rt_torch_rnn_new, (input_size: i64, hidden_size: i64), {
    // Create RNN layer with Xavier-initialized weights
    let weight_ih = Tensor::randn(&[hidden_size, input_size], (Kind::Float, Device::Cpu));
    let std_ih = (2.0 / input_size as f64).sqrt();
    let weight_ih = weight_ih * std_ih;
    let weight_ih_handle = store_tensor(weight_ih);

    let weight_hh = Tensor::randn(&[hidden_size, hidden_size], (Kind::Float, Device::Cpu));
    let std_hh = (2.0 / hidden_size as f64).sqrt();
    let weight_hh = weight_hh * std_hh;
    let weight_hh_handle = store_tensor(weight_hh);

    let bias_ih = Tensor::zeros(&[hidden_size], (Kind::Float, Device::Cpu));
    let bias_ih_handle = store_tensor(bias_ih);

    let bias_hh = Tensor::zeros(&[hidden_size], (Kind::Float, Device::Cpu));
    let bias_hh_handle = store_tensor(bias_hh);

    let layer = RnnLayer {
        weight_ih: weight_ih_handle,
        weight_hh: weight_hh_handle,
        bias_ih: Some(bias_ih_handle),
        bias_hh: Some(bias_hh_handle),
        hidden_size,
        num_layers: 1,
        batch_first: true,
    };

    let handle = store_rnn_layer(layer);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_rnn_forward, (layer: RuntimeValue, input: RuntimeValue, hidden: RuntimeValue), {
    let layer_handle = match layer.as_int() {
        Ok(h) => h,
        Err(_) => return RuntimeValue::NIL,
    };

    let rnn_layer = match get_rnn_layer(layer_handle) {
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

    // Get or create hidden state
    let hidden_tensor = if let Some(h) = value_to_tensor_handle(hidden) {
        get_tensor(h)
    } else {
        None
    };

    let weight_ih = match get_tensor(rnn_layer.weight_ih) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let weight_hh = match get_tensor(rnn_layer.weight_hh) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    // Collect weights into a flat list as expected by rnn_tanh
    let mut params: Vec<Tensor> = vec![weight_ih, weight_hh];
    if let Some(handle) = rnn_layer.bias_ih {
        if let Some(t) = get_tensor(handle) {
            params.push(t);
        }
    }
    if let Some(handle) = rnn_layer.bias_hh {
        if let Some(t) = get_tensor(handle) {
            params.push(t);
        }
    }

    // Create initial hidden if none provided: [num_layers, batch, hidden_size]
    let batch_size = if rnn_layer.batch_first {
        input_tensor.size()[0]
    } else {
        input_tensor.size()[1]
    };
    let hx = hidden_tensor.unwrap_or_else(|| {
        Tensor::zeros(
            &[rnn_layer.num_layers, batch_size, rnn_layer.hidden_size],
            (Kind::Float, Device::Cpu),
        )
    });

    // Use rnn_tanh functional API
    let (output, h_n) = input_tensor.rnn_tanh(
        &hx,
        &params,
        rnn_layer.bias_ih.is_some(),
        rnn_layer.num_layers,
        0.0,   // dropout
        false, // training
        false, // bidirectional
        rnn_layer.batch_first,
    );

    // Return tuple of (output, hidden_n) as a tensor list
    let output_handle = store_tensor(output);
    let hidden_handle = store_tensor(h_n);
    let list_handle = store_tensor_list(vec![output_handle, hidden_handle]);
    RuntimeValue::from_int(list_handle)
});

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(feature = "pytorch")]
    fn test_rnn_new() {
        use super::*;
        let layer = rt_torch_rnn_new(10, 20);
        assert!(layer.is_int());
    }

    #[test]
    #[cfg(feature = "pytorch")]
    fn test_rnn_forward() {
        use super::*;
        // Basic smoke test - would need actual tensors for full test
        let result = rt_torch_rnn_forward(RuntimeValue::NIL, RuntimeValue::NIL, RuntimeValue::NIL);
        assert_eq!(result, RuntimeValue::NIL);
    }
}
