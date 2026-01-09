//! Recurrent Neural Network Layers
//!
//! Provides LSTM and GRU layers for sequence modeling.

#[cfg(feature = "pytorch")]
use super::{next_module_handle, ModuleState, MODULE_REGISTRY};

#[cfg(feature = "pytorch")]
use super::{next_handle, TensorWrapper, TENSOR_REGISTRY};

#[cfg(feature = "pytorch")]
use super::{rt_torch_free, rt_torch_randn, rt_torch_zeros};

#[cfg(feature = "pytorch")]
use tch::Tensor;

/// Helper function to initialize RNN weights for a single direction
#[cfg(feature = "pytorch")]
fn init_rnn_weights(
    num_gates: i64,
    hidden_size: i64,
    input_dim: i64,
) -> Option<(u64, u64, u64, u64)> {
    let weight_ih_shape = vec![num_gates * hidden_size, input_dim];
    let weight_ih = rt_torch_randn(weight_ih_shape.as_ptr(), 2, 0, 0);

    let weight_hh_shape = vec![num_gates * hidden_size, hidden_size];
    let weight_hh = rt_torch_randn(weight_hh_shape.as_ptr(), 2, 0, 0);

    let bias_shape = vec![num_gates * hidden_size];
    let bias_ih = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);
    let bias_hh = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);

    if weight_ih == 0 || weight_hh == 0 || bias_ih == 0 || bias_hh == 0 {
        return None;
    }

    Some((weight_ih, weight_hh, bias_ih, bias_hh))
}

/// Helper function to initialize all RNN layers
#[cfg(feature = "pytorch")]
fn init_rnn_layers(
    num_gates: i64,
    input_size: i64,
    hidden_size: i64,
    num_layers: i64,
    bidirectional: bool,
) -> Option<Vec<(u64, u64, u64, u64)>> {
    let num_directions = if bidirectional { 2 } else { 1 };
    let mut weights = Vec::new();

    for layer_idx in 0..num_layers {
        let input_dim = if layer_idx == 0 {
            input_size
        } else {
            hidden_size * num_directions
        };

        // Forward direction weights
        let Some(layer_weights) = init_rnn_weights(num_gates, hidden_size, input_dim) else {
            // Cleanup on failure
            for (wih, whh, bih, bhh) in &weights {
                rt_torch_free(*wih);
                rt_torch_free(*whh);
                rt_torch_free(*bih);
                rt_torch_free(*bhh);
            }
            return None;
        };
        weights.push(layer_weights);

        // Backward direction weights (if bidirectional)
        if bidirectional {
            let Some(layer_weights_rev) = init_rnn_weights(num_gates, hidden_size, input_dim)
            else {
                // Cleanup on failure
                for (wih, whh, bih, bhh) in &weights {
                    rt_torch_free(*wih);
                    rt_torch_free(*whh);
                    rt_torch_free(*bih);
                    rt_torch_free(*bhh);
                }
                return None;
            };
            weights.push(layer_weights_rev);
        }
    }

    Some(weights)
}

/// Helper to build parameter list from weight handles
#[cfg(feature = "pytorch")]
fn build_rnn_params(weights: &[(u64, u64, u64, u64)]) -> Vec<Tensor> {
    let mut params: Vec<Tensor> = Vec::new();
    for (weight_ih, weight_hh, bias_ih, bias_hh) in weights {
        let registry = TENSOR_REGISTRY.lock();
        params.push(registry.get(weight_ih).unwrap().0.shallow_clone());
        params.push(registry.get(weight_hh).unwrap().0.shallow_clone());
        params.push(registry.get(bias_ih).unwrap().0.shallow_clone());
        params.push(registry.get(bias_hh).unwrap().0.shallow_clone());
    }
    params
}

/// Helper to get or create initial hidden state
#[cfg(feature = "pytorch")]
fn get_or_create_hidden_state(
    h_handle: u64,
    num_layers: i64,
    num_directions: i64,
    batch_size: i64,
    hidden_size: i64,
) -> Option<Tensor> {
    if h_handle == 0 {
        let shape = vec![num_layers * num_directions, batch_size, hidden_size];
        let h = rt_torch_zeros(shape.as_ptr(), 3, 0, 0);
        let registry = TENSOR_REGISTRY.lock();
        Some(registry.get(&h).cloned()?.0.shallow_clone())
    } else {
        let registry = TENSOR_REGISTRY.lock();
        Some(registry.get(&h_handle).cloned()?.0.shallow_clone())
    }
}

/// Create an LSTM module
/// input_size: size of input features
/// hidden_size: size of hidden state
/// num_layers: number of recurrent layers
/// bidirectional: 1 for bidirectional, 0 for unidirectional
#[no_mangle]
pub extern "C" fn rt_torch_lstm_new(
    input_size: i64,
    hidden_size: i64,
    num_layers: i64,
    bidirectional: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if input_size <= 0 || hidden_size <= 0 || num_layers <= 0 {
            return 0;
        }

        let is_bidirectional = bidirectional != 0;

        // LSTM has 4 gates: input, forget, cell, output
        let Some(weights) =
            init_rnn_layers(4, input_size, hidden_size, num_layers, is_bidirectional)
        else {
            return 0;
        };

        let module = ModuleState::LSTM {
            input_size,
            hidden_size,
            num_layers,
            bidirectional: is_bidirectional,
            weights,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY
            .lock()
            .insert(handle, std::sync::Arc::new(module));

        tracing::debug!(
            "rt_torch_lstm_new: input={} hidden={} layers={} bidir={} -> {}",
            input_size,
            hidden_size,
            num_layers,
            bidirectional,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_size, hidden_size, num_layers, bidirectional);
        0
    }
}

/// LSTM forward pass
/// Returns handle to output tensor: [seq_len, batch, hidden_size * num_directions]
/// h0_handle: initial hidden state [num_layers * num_directions, batch, hidden_size] (0 for zeros)
/// c0_handle: initial cell state (0 for zeros)
/// Returns: (output_handle, (hn_handle, cn_handle)) encoded as a tuple - for now just output
#[no_mangle]
pub extern "C" fn rt_torch_lstm_forward(
    module_handle: u64,
    input_handle: u64,
    h0_handle: u64,
    c0_handle: u64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle).cloned() else {
            return 0;
        };
        drop(module_registry);

        match module.as_ref() {
            ModuleState::LSTM {
                hidden_size,
                num_layers,
                bidirectional,
                weights,
                ..
            } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(input) = tensor_registry.get(&input_handle).cloned() else {
                    return 0;
                };
                drop(tensor_registry);

                let num_directions = if *bidirectional { 2 } else { 1 };

                // Get input shape: [seq_len, batch, input_size]
                let input_shape = input.0.size();
                if input_shape.len() != 3 {
                    tracing::error!("LSTM input must be 3D: [seq_len, batch, input_size]");
                    return 0;
                }

                let batch_size = input_shape[1];

                // Initialize h0 and c0 if not provided
                let Some(h0) = get_or_create_hidden_state(
                    h0_handle,
                    *num_layers,
                    num_directions,
                    batch_size,
                    *hidden_size,
                ) else {
                    return 0;
                };
                let Some(c0) = get_or_create_hidden_state(
                    c0_handle,
                    *num_layers,
                    num_directions,
                    batch_size,
                    *hidden_size,
                ) else {
                    return 0;
                };

                // Build parameter lists for tch-rs LSTM
                let params = build_rnn_params(weights);

                // Call tch's lstm function
                let (output, _hn, _cn) = input.0.lstm(
                    &[h0, c0],
                    &params,
                    true,           // has_biases
                    *num_layers,    // num_layers
                    0.0,            // dropout
                    false,          // train mode
                    *bidirectional, // bidirectional
                    false,          // batch_first
                );

                let handle = next_handle();
                TENSOR_REGISTRY
                    .lock()
                    .insert(handle, std::sync::Arc::new(TensorWrapper(output)));

                tracing::debug!(
                    "rt_torch_lstm_forward: module={} input={} -> output={}",
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
        let _ = (module_handle, input_handle, h0_handle, c0_handle);
        0
    }
}

/// Create a GRU module
#[no_mangle]
pub extern "C" fn rt_torch_gru_new(
    input_size: i64,
    hidden_size: i64,
    num_layers: i64,
    bidirectional: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if input_size <= 0 || hidden_size <= 0 || num_layers <= 0 {
            return 0;
        }

        let is_bidirectional = bidirectional != 0;

        // GRU has 3 gates: reset, input, new
        let Some(weights) =
            init_rnn_layers(3, input_size, hidden_size, num_layers, is_bidirectional)
        else {
            return 0;
        };

        let module = ModuleState::GRU {
            input_size,
            hidden_size,
            num_layers,
            bidirectional: is_bidirectional,
            weights,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY
            .lock()
            .insert(handle, std::sync::Arc::new(module));

        tracing::debug!(
            "rt_torch_gru_new: input={} hidden={} layers={} bidir={} -> {}",
            input_size,
            hidden_size,
            num_layers,
            bidirectional,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_size, hidden_size, num_layers, bidirectional);
        0
    }
}

/// GRU forward pass
/// Returns output tensor: [seq_len, batch, hidden_size * num_directions]
#[no_mangle]
pub extern "C" fn rt_torch_gru_forward(
    module_handle: u64,
    input_handle: u64,
    h0_handle: u64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle).cloned() else {
            return 0;
        };
        drop(module_registry);

        match module.as_ref() {
            ModuleState::GRU {
                hidden_size,
                num_layers,
                bidirectional,
                weights,
                ..
            } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(input) = tensor_registry.get(&input_handle).cloned() else {
                    return 0;
                };
                drop(tensor_registry);

                let num_directions = if *bidirectional { 2 } else { 1 };

                // Get input shape: [seq_len, batch, input_size]
                let input_shape = input.0.size();
                if input_shape.len() != 3 {
                    tracing::error!("GRU input must be 3D: [seq_len, batch, input_size]");
                    return 0;
                }

                let batch_size = input_shape[1];

                // Initialize h0 if not provided
                let Some(h0) = get_or_create_hidden_state(
                    h0_handle,
                    *num_layers,
                    num_directions,
                    batch_size,
                    *hidden_size,
                ) else {
                    return 0;
                };

                // Build parameter lists
                let params = build_rnn_params(weights);

                // Call tch's gru function
                let (output, _hn) = input.0.gru(
                    &h0,
                    &params,
                    true,           // has_biases
                    *num_layers,    // num_layers
                    0.0,            // dropout
                    false,          // train
                    *bidirectional, // bidirectional
                    false,          // batch_first
                );

                let handle = next_handle();
                TENSOR_REGISTRY
                    .lock()
                    .insert(handle, std::sync::Arc::new(TensorWrapper(output)));

                tracing::debug!(
                    "rt_torch_gru_forward: module={} input={} -> output={}",
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
        let _ = (module_handle, input_handle, h0_handle);
        0
    }
}
