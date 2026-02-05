//! Transformer encoder and decoder layers
//!
//! Provides TransformerEncoderLayer and TransformerDecoderLayer with self-attention,
//! cross-attention (decoder only), feedforward networks, and layer normalization.

use crate::value::RuntimeValue;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Mutex;

#[cfg(feature = "pytorch")]
use super::super::storage::{get_tensor, store_tensor, value_to_tensor_handle};

#[cfg(feature = "pytorch")]
use super::attention::rt_torch_multihead_attention_new;

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
// TransformerEncoderLayer Storage
// ============================================================================

/// TransformerEncoderLayer
#[cfg(feature = "pytorch")]
#[derive(Clone)]
struct TransformerEncoderLayer {
    self_attn: i64, // MultiheadAttention handle
    linear1_weight: i64,
    linear1_bias: i64,
    linear2_weight: i64,
    linear2_bias: i64,
    norm1_weight: i64,
    norm1_bias: i64,
    norm2_weight: i64,
    norm2_bias: i64,
    d_model: i64,
    nhead: i64,
    dim_feedforward: i64,
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref TRANSFORMER_ENCODER_LAYER_MAP: Mutex<HashMap<i64, TransformerEncoderLayer>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static TRANSFORMER_ENCODER_LAYER_COUNTER: AtomicI64 = AtomicI64::new(1);

#[cfg(feature = "pytorch")]
fn store_transformer_encoder_layer(layer: TransformerEncoderLayer) -> i64 {
    let handle = TRANSFORMER_ENCODER_LAYER_COUNTER.fetch_add(1, Ordering::SeqCst);
    TRANSFORMER_ENCODER_LAYER_MAP.lock().unwrap().insert(handle, layer);
    handle
}

#[cfg(feature = "pytorch")]
fn get_transformer_encoder_layer(handle: i64) -> Option<TransformerEncoderLayer> {
    TRANSFORMER_ENCODER_LAYER_MAP.lock().unwrap().get(&handle).cloned()
}

// ============================================================================
// TransformerDecoderLayer Storage
// ============================================================================

/// TransformerDecoderLayer
#[cfg(feature = "pytorch")]
#[derive(Clone)]
struct TransformerDecoderLayer {
    self_attn: i64,  // MultiheadAttention handle
    cross_attn: i64, // MultiheadAttention handle
    linear1_weight: i64,
    linear1_bias: i64,
    linear2_weight: i64,
    linear2_bias: i64,
    norm1_weight: i64,
    norm1_bias: i64,
    norm2_weight: i64,
    norm2_bias: i64,
    norm3_weight: i64,
    norm3_bias: i64,
    d_model: i64,
    nhead: i64,
    dim_feedforward: i64,
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref TRANSFORMER_DECODER_LAYER_MAP: Mutex<HashMap<i64, TransformerDecoderLayer>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static TRANSFORMER_DECODER_LAYER_COUNTER: AtomicI64 = AtomicI64::new(1);

#[cfg(feature = "pytorch")]
fn store_transformer_decoder_layer(layer: TransformerDecoderLayer) -> i64 {
    let handle = TRANSFORMER_DECODER_LAYER_COUNTER.fetch_add(1, Ordering::SeqCst);
    TRANSFORMER_DECODER_LAYER_MAP.lock().unwrap().insert(handle, layer);
    handle
}

#[cfg(feature = "pytorch")]
fn get_transformer_decoder_layer(handle: i64) -> Option<TransformerDecoderLayer> {
    TRANSFORMER_DECODER_LAYER_MAP.lock().unwrap().get(&handle).cloned()
}

// ============================================================================
// TransformerEncoderLayer Operations
// ============================================================================

pytorch_fn!(rt_torch_transformer_encoder_layer_new, (d_model: i64, nhead: i64), {
    let dim_feedforward = 4 * d_model; // Standard transformer uses 4x

    // Create self-attention
    let self_attn_handle = match rt_torch_multihead_attention_new(d_model, nhead).as_int() {
        Ok(h) => h,
        Err(_) => return RuntimeValue::NIL,
    };

    // Feedforward layers
    let linear1_weight = Tensor::randn(&[dim_feedforward, d_model], (Kind::Float, Device::Cpu));
    let std1 = (2.0 / d_model as f64).sqrt();
    let linear1_weight = linear1_weight * std1;
    let linear1_weight_handle = store_tensor(linear1_weight);

    let linear1_bias = Tensor::zeros(&[dim_feedforward], (Kind::Float, Device::Cpu));
    let linear1_bias_handle = store_tensor(linear1_bias);

    let linear2_weight = Tensor::randn(&[d_model, dim_feedforward], (Kind::Float, Device::Cpu));
    let std2 = (2.0 / dim_feedforward as f64).sqrt();
    let linear2_weight = linear2_weight * std2;
    let linear2_weight_handle = store_tensor(linear2_weight);

    let linear2_bias = Tensor::zeros(&[d_model], (Kind::Float, Device::Cpu));
    let linear2_bias_handle = store_tensor(linear2_bias);

    // Layer normalization parameters
    let norm1_weight = Tensor::ones(&[d_model], (Kind::Float, Device::Cpu));
    let norm1_weight_handle = store_tensor(norm1_weight);
    let norm1_bias = Tensor::zeros(&[d_model], (Kind::Float, Device::Cpu));
    let norm1_bias_handle = store_tensor(norm1_bias);

    let norm2_weight = Tensor::ones(&[d_model], (Kind::Float, Device::Cpu));
    let norm2_weight_handle = store_tensor(norm2_weight);
    let norm2_bias = Tensor::zeros(&[d_model], (Kind::Float, Device::Cpu));
    let norm2_bias_handle = store_tensor(norm2_bias);

    let layer = TransformerEncoderLayer {
        self_attn: self_attn_handle,
        linear1_weight: linear1_weight_handle,
        linear1_bias: linear1_bias_handle,
        linear2_weight: linear2_weight_handle,
        linear2_bias: linear2_bias_handle,
        norm1_weight: norm1_weight_handle,
        norm1_bias: norm1_bias_handle,
        norm2_weight: norm2_weight_handle,
        norm2_bias: norm2_bias_handle,
        d_model,
        nhead,
        dim_feedforward,
    };

    let handle = store_transformer_encoder_layer(layer);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_transformer_encoder_layer_forward, (layer: RuntimeValue, src: RuntimeValue), {
    use super::attention::rt_torch_multihead_attention_forward;

    let layer_handle = match layer.as_int() {
        Ok(h) => h,
        Err(_) => return RuntimeValue::NIL,
    };

    let enc_layer = match get_transformer_encoder_layer(layer_handle) {
        Some(l) => l,
        None => return RuntimeValue::NIL,
    };

    let src_tensor = match value_to_tensor_handle(src).and_then(get_tensor) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    // Self-attention
    let attn_output = rt_torch_multihead_attention_forward(
        RuntimeValue::from_int(enc_layer.self_attn),
        RuntimeValue::from_int(store_tensor(src_tensor.shallow_clone())),
        RuntimeValue::from_int(store_tensor(src_tensor.shallow_clone())),
        RuntimeValue::from_int(store_tensor(src_tensor.shallow_clone())),
    );

    let attn_output = match attn_output.as_int().ok().and_then(get_tensor) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    // Residual + LayerNorm
    let norm1_weight = match get_tensor(enc_layer.norm1_weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let norm1_bias = match get_tensor(enc_layer.norm1_bias) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let x = &src_tensor + &attn_output;
    let x = x.layer_norm(&[enc_layer.d_model], Some(&norm1_weight), Some(&norm1_bias), 1e-5, true);

    // Feedforward
    let linear1_weight = match get_tensor(enc_layer.linear1_weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let linear1_bias = match get_tensor(enc_layer.linear1_bias) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let linear2_weight = match get_tensor(enc_layer.linear2_weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let linear2_bias = match get_tensor(enc_layer.linear2_bias) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let ff = x.matmul(&linear1_weight.transpose(-2, -1)) + &linear1_bias;
    let ff = ff.relu();
    let ff = ff.matmul(&linear2_weight.transpose(-2, -1)) + &linear2_bias;

    // Residual + LayerNorm
    let norm2_weight = match get_tensor(enc_layer.norm2_weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let norm2_bias = match get_tensor(enc_layer.norm2_bias) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let output = &x + &ff;
    let output = output.layer_norm(&[enc_layer.d_model], Some(&norm2_weight), Some(&norm2_bias), 1e-5, true);

    let handle = store_tensor(output);
    RuntimeValue::from_int(handle)
});

// ============================================================================
// TransformerDecoderLayer Operations
// ============================================================================

pytorch_fn!(rt_torch_transformer_decoder_layer_new, (d_model: i64, nhead: i64), {
    let dim_feedforward = 4 * d_model;

    // Self-attention
    let self_attn_handle = match rt_torch_multihead_attention_new(d_model, nhead).as_int() {
        Ok(h) => h,
        Err(_) => return RuntimeValue::NIL,
    };

    // Cross-attention
    let cross_attn_handle = match rt_torch_multihead_attention_new(d_model, nhead).as_int() {
        Ok(h) => h,
        Err(_) => return RuntimeValue::NIL,
    };

    // Feedforward layers
    let linear1_weight = Tensor::randn(&[dim_feedforward, d_model], (Kind::Float, Device::Cpu));
    let std1 = (2.0 / d_model as f64).sqrt();
    let linear1_weight = linear1_weight * std1;
    let linear1_weight_handle = store_tensor(linear1_weight);

    let linear1_bias = Tensor::zeros(&[dim_feedforward], (Kind::Float, Device::Cpu));
    let linear1_bias_handle = store_tensor(linear1_bias);

    let linear2_weight = Tensor::randn(&[d_model, dim_feedforward], (Kind::Float, Device::Cpu));
    let std2 = (2.0 / dim_feedforward as f64).sqrt();
    let linear2_weight = linear2_weight * std2;
    let linear2_weight_handle = store_tensor(linear2_weight);

    let linear2_bias = Tensor::zeros(&[d_model], (Kind::Float, Device::Cpu));
    let linear2_bias_handle = store_tensor(linear2_bias);

    // Layer normalization parameters (3 norms for decoder)
    let norm1_weight = Tensor::ones(&[d_model], (Kind::Float, Device::Cpu));
    let norm1_weight_handle = store_tensor(norm1_weight);
    let norm1_bias = Tensor::zeros(&[d_model], (Kind::Float, Device::Cpu));
    let norm1_bias_handle = store_tensor(norm1_bias);

    let norm2_weight = Tensor::ones(&[d_model], (Kind::Float, Device::Cpu));
    let norm2_weight_handle = store_tensor(norm2_weight);
    let norm2_bias = Tensor::zeros(&[d_model], (Kind::Float, Device::Cpu));
    let norm2_bias_handle = store_tensor(norm2_bias);

    let norm3_weight = Tensor::ones(&[d_model], (Kind::Float, Device::Cpu));
    let norm3_weight_handle = store_tensor(norm3_weight);
    let norm3_bias = Tensor::zeros(&[d_model], (Kind::Float, Device::Cpu));
    let norm3_bias_handle = store_tensor(norm3_bias);

    let layer = TransformerDecoderLayer {
        self_attn: self_attn_handle,
        cross_attn: cross_attn_handle,
        linear1_weight: linear1_weight_handle,
        linear1_bias: linear1_bias_handle,
        linear2_weight: linear2_weight_handle,
        linear2_bias: linear2_bias_handle,
        norm1_weight: norm1_weight_handle,
        norm1_bias: norm1_bias_handle,
        norm2_weight: norm2_weight_handle,
        norm2_bias: norm2_bias_handle,
        norm3_weight: norm3_weight_handle,
        norm3_bias: norm3_bias_handle,
        d_model,
        nhead,
        dim_feedforward,
    };

    let handle = store_transformer_decoder_layer(layer);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_transformer_decoder_layer_forward,
    (layer: RuntimeValue, tgt: RuntimeValue, memory: RuntimeValue), {
    use super::attention::rt_torch_multihead_attention_forward;

    let layer_handle = match layer.as_int() {
        Ok(h) => h,
        Err(_) => return RuntimeValue::NIL,
    };

    let dec_layer = match get_transformer_decoder_layer(layer_handle) {
        Some(l) => l,
        None => return RuntimeValue::NIL,
    };

    let tgt_tensor = match value_to_tensor_handle(tgt).and_then(get_tensor) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let memory_tensor = match value_to_tensor_handle(memory).and_then(get_tensor) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    // Self-attention on target
    let self_attn_output = rt_torch_multihead_attention_forward(
        RuntimeValue::from_int(dec_layer.self_attn),
        RuntimeValue::from_int(store_tensor(tgt_tensor.shallow_clone())),
        RuntimeValue::from_int(store_tensor(tgt_tensor.shallow_clone())),
        RuntimeValue::from_int(store_tensor(tgt_tensor.shallow_clone())),
    );

    let self_attn_output = match self_attn_output.as_int().ok().and_then(get_tensor) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    // Residual + LayerNorm 1
    let norm1_weight = match get_tensor(dec_layer.norm1_weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let norm1_bias = match get_tensor(dec_layer.norm1_bias) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let x = &tgt_tensor + &self_attn_output;
    let x = x.layer_norm(&[dec_layer.d_model], Some(&norm1_weight), Some(&norm1_bias), 1e-5, true);

    // Cross-attention (query=x, key=memory, value=memory)
    let cross_attn_output = rt_torch_multihead_attention_forward(
        RuntimeValue::from_int(dec_layer.cross_attn),
        RuntimeValue::from_int(store_tensor(x.shallow_clone())),
        RuntimeValue::from_int(store_tensor(memory_tensor.shallow_clone())),
        RuntimeValue::from_int(store_tensor(memory_tensor.shallow_clone())),
    );

    let cross_attn_output = match cross_attn_output.as_int().ok().and_then(get_tensor) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    // Residual + LayerNorm 2
    let norm2_weight = match get_tensor(dec_layer.norm2_weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let norm2_bias = match get_tensor(dec_layer.norm2_bias) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let x = &x + &cross_attn_output;
    let x = x.layer_norm(&[dec_layer.d_model], Some(&norm2_weight), Some(&norm2_bias), 1e-5, true);

    // Feedforward
    let linear1_weight = match get_tensor(dec_layer.linear1_weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let linear1_bias = match get_tensor(dec_layer.linear1_bias) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let linear2_weight = match get_tensor(dec_layer.linear2_weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let linear2_bias = match get_tensor(dec_layer.linear2_bias) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let ff = x.matmul(&linear1_weight.transpose(-2, -1)) + &linear1_bias;
    let ff = ff.relu();
    let ff = ff.matmul(&linear2_weight.transpose(-2, -1)) + &linear2_bias;

    // Residual + LayerNorm 3
    let norm3_weight = match get_tensor(dec_layer.norm3_weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let norm3_bias = match get_tensor(dec_layer.norm3_bias) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let output = &x + &ff;
    let output = output.layer_norm(&[dec_layer.d_model], Some(&norm3_weight), Some(&norm3_bias), 1e-5, true);

    let handle = store_tensor(output);
    RuntimeValue::from_int(handle)
});

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(feature = "pytorch")]
    fn test_transformer_encoder_layer_new() {
        use super::*;
        let layer = rt_torch_transformer_encoder_layer_new(512, 8);
        assert!(layer.is_int());
    }

    #[test]
    #[cfg(feature = "pytorch")]
    fn test_transformer_decoder_layer_new() {
        use super::*;
        let layer = rt_torch_transformer_decoder_layer_new(512, 8);
        assert!(layer.is_int());
    }
}
