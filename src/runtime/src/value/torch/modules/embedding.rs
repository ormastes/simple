//! Embedding Layer
//!
//! Provides learnable lookup tables for discrete tokens.

#[cfg(feature = "pytorch")]
use super::{ModuleState, MODULE_REGISTRY, next_module_handle};

#[cfg(feature = "pytorch")]
use super::{TENSOR_REGISTRY, TensorWrapper, next_handle};

#[cfg(feature = "pytorch")]
use super::{rt_torch_randn, rt_torch_free, rt_torch_set_requires_grad, rt_torch_detach};

#[cfg(feature = "pytorch")]
use tch::Kind as TchKind;

/// Create an Embedding module
/// num_embeddings: size of the vocabulary
/// embedding_dim: size of each embedding vector
/// padding_idx: if specified, entries at this index do not contribute to gradient (-1 for none)
#[no_mangle]
pub extern "C" fn rt_torch_embedding_new(
    num_embeddings: i64,
    embedding_dim: i64,
    padding_idx: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if num_embeddings <= 0 || embedding_dim <= 0 {
            return 0;
        }

        // Create embedding weight matrix [num_embeddings, embedding_dim]
        let weight_shape = vec![num_embeddings, embedding_dim];
        let weight = rt_torch_randn(weight_shape.as_ptr(), 2, 0, 0);
        if weight == 0 {
            return 0;
        }

        // Set requires_grad for training
        let weight_with_grad = rt_torch_set_requires_grad(weight, 1);
        rt_torch_free(weight);

        // If padding_idx is specified, initialize that row to zeros
        if padding_idx >= 0 && padding_idx < num_embeddings {
            // This would require indexing, for now we skip it
            // PyTorch does: weight[padding_idx].fill_(0)
        }

        let padding = if padding_idx >= 0 {
            Some(padding_idx)
        } else {
            None
        };

        let module = ModuleState::Embedding {
            num_embeddings,
            embedding_dim,
            weight: weight_with_grad,
            padding_idx: padding,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, std::sync::Arc::new(module));

        tracing::debug!(
            "rt_torch_embedding_new: handle={} vocab={} dim={} pad={:?}",
            handle,
            num_embeddings,
            embedding_dim,
            padding
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (num_embeddings, embedding_dim, padding_idx);
        0
    }
}

/// Forward pass through Embedding layer
/// module_handle: handle to Embedding module
/// input_handle: handle to input tensor of indices (LongTensor)
/// Returns: embedded tensor of shape [input_shape..., embedding_dim]
#[no_mangle]
pub extern "C" fn rt_torch_embedding_forward(
    module_handle: u64,
    input_handle: u64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle).cloned() else {
            return 0;
        };
        drop(module_registry);

        let ModuleState::Embedding { weight, embedding_dim, .. } = module.as_ref() else {
            return 0;
        };

        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(input) = tensor_registry.get(&input_handle).cloned() else {
            return 0;
        };
        let Some(w) = tensor_registry.get(weight).cloned() else {
            return 0;
        };
        drop(tensor_registry);

        // Convert input to Long type if needed
        let input_long = input.0.to_kind(TchKind::Int64);

        // Apply embedding: gather rows from weight matrix using index_select
        // Flatten input to 1D for indexing, then reshape back
        let input_shape = input_long.size();
        let input_flat = input_long.view(-1);

        // Select rows from weight matrix
        let result_flat = w.0.index_select(0, &input_flat);

        // Reshape to [..., embedding_dim]
        let mut output_shape = input_shape.clone();
        output_shape.push(*embedding_dim);
        let result = result_flat.view(output_shape.as_slice());

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, std::sync::Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_embedding_forward: module={} input={} output={}",
            module_handle,
            input_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (module_handle, input_handle);
        0
    }
}

/// Get weight tensor from Embedding layer
#[no_mangle]
pub extern "C" fn rt_torch_embedding_get_weight(module_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle) else {
            return 0;
        };

        match module.as_ref() {
            ModuleState::Embedding { weight, .. } => *weight,
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = module_handle;
        0
    }
}

/// Create embedding from pretrained weights
/// weight_handle: handle to pretrained weight tensor [num_embeddings, embedding_dim]
/// freeze: whether to freeze the embeddings (1) or allow training (0)
/// padding_idx: optional padding index (-1 for none)
#[no_mangle]
pub extern "C" fn rt_torch_embedding_from_pretrained(
    weight_handle: u64,
    freeze: i32,
    padding_idx: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(weight) = tensor_registry.get(&weight_handle).cloned() else {
            return 0;
        };
        drop(tensor_registry);

        // Get shape to extract num_embeddings and embedding_dim
        let shape = weight.0.size();
        if shape.len() != 2 {
            return 0;
        }

        let num_embeddings = shape[0];
        let embedding_dim = shape[1];

        // Clone or use weight directly based on freeze
        let weight_to_use = if freeze != 0 {
            // Frozen: detach from computation graph
            rt_torch_detach(weight_handle)
        } else {
            // Trainable: set requires_grad
            rt_torch_set_requires_grad(weight_handle, 1)
        };

        let padding = if padding_idx >= 0 {
            Some(padding_idx)
        } else {
            None
        };

        let module = ModuleState::Embedding {
            num_embeddings,
            embedding_dim,
            weight: weight_to_use,
            padding_idx: padding,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, std::sync::Arc::new(module));

        tracing::debug!(
            "rt_torch_embedding_from_pretrained: handle={} freeze={} pad={:?}",
            handle,
            freeze,
            padding
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (weight_handle, freeze, padding_idx);
        0
    }
}
