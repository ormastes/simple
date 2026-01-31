//! Attention mechanisms for neural networks
//!
//! Provides MultiheadAttention and PositionalEncoding for transformer architectures.

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
// MultiheadAttention Layer Storage
// ============================================================================

/// MultiheadAttention layer
#[cfg(feature = "pytorch")]
#[derive(Clone)]
struct MultiheadAttentionLayer {
    in_proj_weight: i64, // [3 * embed_dim, embed_dim]
    in_proj_bias: Option<i64>,
    out_proj_weight: i64, // [embed_dim, embed_dim]
    out_proj_bias: Option<i64>,
    embed_dim: i64,
    num_heads: i64,
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref MULTIHEAD_ATTENTION_MAP: Mutex<HashMap<i64, MultiheadAttentionLayer>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static MULTIHEAD_ATTENTION_COUNTER: AtomicI64 = AtomicI64::new(1);

#[cfg(feature = "pytorch")]
fn store_multihead_attention_layer(layer: MultiheadAttentionLayer) -> i64 {
    let handle = MULTIHEAD_ATTENTION_COUNTER.fetch_add(1, Ordering::SeqCst);
    MULTIHEAD_ATTENTION_MAP.lock().unwrap().insert(handle, layer);
    handle
}

#[cfg(feature = "pytorch")]
fn get_multihead_attention_layer(handle: i64) -> Option<MultiheadAttentionLayer> {
    MULTIHEAD_ATTENTION_MAP.lock().unwrap().get(&handle).cloned()
}

// ============================================================================
// Positional Encoding Storage
// ============================================================================

/// Positional encoding: precomputed encoding tensor
#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref POSITIONAL_ENCODING_MAP: Mutex<HashMap<i64, i64>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static POSITIONAL_ENCODING_COUNTER: AtomicI64 = AtomicI64::new(1);

#[cfg(feature = "pytorch")]
fn store_positional_encoding(tensor_handle: i64) -> i64 {
    let handle = POSITIONAL_ENCODING_COUNTER.fetch_add(1, Ordering::SeqCst);
    POSITIONAL_ENCODING_MAP.lock().unwrap().insert(handle, tensor_handle);
    handle
}

// ============================================================================
// MultiheadAttention Operations
// ============================================================================

pytorch_fn!(rt_torch_multihead_attention_new, (embed_dim: i64, num_heads: i64), {
    // in_proj_weight: [3 * embed_dim, embed_dim] for Q, K, V projections
    let in_proj_weight = Tensor::randn(&[3 * embed_dim, embed_dim], (Kind::Float, Device::Cpu));
    let std_in = (2.0 / embed_dim as f64).sqrt();
    let in_proj_weight = in_proj_weight * std_in;
    let in_proj_weight_handle = store_tensor(in_proj_weight);

    let in_proj_bias = Tensor::zeros(&[3 * embed_dim], (Kind::Float, Device::Cpu));
    let in_proj_bias_handle = store_tensor(in_proj_bias);

    // out_proj_weight: [embed_dim, embed_dim]
    let out_proj_weight = Tensor::randn(&[embed_dim, embed_dim], (Kind::Float, Device::Cpu));
    let out_proj_weight = out_proj_weight * std_in;
    let out_proj_weight_handle = store_tensor(out_proj_weight);

    let out_proj_bias = Tensor::zeros(&[embed_dim], (Kind::Float, Device::Cpu));
    let out_proj_bias_handle = store_tensor(out_proj_bias);

    let layer = MultiheadAttentionLayer {
        in_proj_weight: in_proj_weight_handle,
        in_proj_bias: Some(in_proj_bias_handle),
        out_proj_weight: out_proj_weight_handle,
        out_proj_bias: Some(out_proj_bias_handle),
        embed_dim,
        num_heads,
    };

    let handle = store_multihead_attention_layer(layer);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_multihead_attention_forward,
    (layer: RuntimeValue, query: RuntimeValue, key: RuntimeValue, value: RuntimeValue), {
    let layer_handle = match layer.as_int() {
        Ok(h) => h,
        Err(_) => return RuntimeValue::NIL,
    };

    let mha_layer = match get_multihead_attention_layer(layer_handle) {
        Some(l) => l,
        None => return RuntimeValue::NIL,
    };

    let query_tensor = match value_to_tensor_handle(query).and_then(get_tensor) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let key_tensor = match value_to_tensor_handle(key).and_then(get_tensor) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let value_tensor = match value_to_tensor_handle(value).and_then(get_tensor) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let in_proj_weight = match get_tensor(mha_layer.in_proj_weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let out_proj_weight = match get_tensor(mha_layer.out_proj_weight) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let in_proj_bias = mha_layer.in_proj_bias.and_then(get_tensor);
    let out_proj_bias = mha_layer.out_proj_bias.and_then(get_tensor);

    // Use scaled_dot_product_attention for the core attention computation
    // First, compute Q, K, V projections
    let qkv = query_tensor.matmul(&in_proj_weight.transpose(-2, -1));
    let qkv = if let Some(ref bias) = in_proj_bias {
        qkv + bias
    } else {
        qkv
    };

    // Split into Q, K, V
    let chunks = qkv.chunk(3, -1);
    let q = &chunks[0];
    let k = &chunks[1];
    let v = &chunks[2];

    // Reshape for multi-head attention: [batch, seq, heads, head_dim]
    let head_dim = mha_layer.embed_dim / mha_layer.num_heads;
    let batch_size = q.size()[0];
    let seq_len = q.size()[1];

    let q = q
        .view([batch_size, seq_len, mha_layer.num_heads, head_dim])
        .transpose(1, 2);
    let k = key_tensor.matmul(
        &in_proj_weight
            .narrow(0, mha_layer.embed_dim, mha_layer.embed_dim)
            .transpose(-2, -1),
    );
    let k = k.view([batch_size, -1, mha_layer.num_heads, head_dim]).transpose(1, 2);
    let v = value_tensor.matmul(
        &in_proj_weight
            .narrow(0, 2 * mha_layer.embed_dim, mha_layer.embed_dim)
            .transpose(-2, -1),
    );
    let v = v.view([batch_size, -1, mha_layer.num_heads, head_dim]).transpose(1, 2);

    // Scaled dot-product attention
    let scale = (head_dim as f64).sqrt();
    let scores = q.matmul(&k.transpose(-2, -1)) / scale;
    let attn_weights = scores.softmax(-1, Kind::Float);
    let attn_output = attn_weights.matmul(&v);

    // Reshape back: [batch, seq, embed_dim]
    let attn_output = attn_output
        .transpose(1, 2)
        .contiguous()
        .view([batch_size, seq_len, mha_layer.embed_dim]);

    // Output projection
    let output = attn_output.matmul(&out_proj_weight.transpose(-2, -1));
    let output = if let Some(ref bias) = out_proj_bias {
        output + bias
    } else {
        output
    };

    let handle = store_tensor(output);
    RuntimeValue::from_int(handle)
});

// ============================================================================
// Positional Encoding Operations
// ============================================================================

pytorch_fn!(rt_torch_positional_encoding_new, (d_model: i64, max_len: i64), {
    // Create sinusoidal positional encoding
    // PE(pos, 2i) = sin(pos / 10000^(2i/d_model))
    // PE(pos, 2i+1) = cos(pos / 10000^(2i/d_model))
    let position = Tensor::arange(max_len, (Kind::Float, Device::Cpu)).unsqueeze(1);
    let div_term = (Tensor::arange_start_step(0, d_model, 2, (Kind::Float, Device::Cpu))
        * (-((10000.0_f64).ln()) / d_model as f64))
        .exp();

    // Fill even indices with sin
    let sin_vals = (&position * &div_term).sin();
    let cos_vals = (&position * &div_term).cos();

    // Interleave sin and cos values
    let mut pe_vec = Vec::new();
    for i in 0..max_len {
        let mut row = Vec::new();
        for j in 0..d_model / 2 {
            row.push(sin_vals.double_value(&[i, j]));
            row.push(cos_vals.double_value(&[i, j]));
        }
        // Handle odd d_model
        if d_model % 2 == 1 {
            row.push(sin_vals.double_value(&[i, d_model / 2]));
        }
        pe_vec.extend(row);
    }

    let pe_tensor = Tensor::from_slice(&pe_vec).view([max_len, d_model]);
    let pe_handle = store_tensor(pe_tensor);

    let handle = store_positional_encoding(pe_handle);
    RuntimeValue::from_int(handle)
});

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(feature = "pytorch")]
    fn test_multihead_attention_new() {
        use super::*;
        let layer = rt_torch_multihead_attention_new(512, 8);
        assert!(layer.is_int());
    }

    #[test]
    #[cfg(feature = "pytorch")]
    fn test_positional_encoding_new() {
        use super::*;
        let encoding = rt_torch_positional_encoding_new(512, 1000);
        assert!(encoding.is_int());
    }
}
