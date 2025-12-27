//! Optimizers for neural network training (SGD, Adam, AdamW)

#[cfg(feature = "pytorch")]
use parking_lot::Mutex;

#[cfg(feature = "pytorch")]
use std::collections::HashMap;

#[cfg(feature = "pytorch")]
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "pytorch")]
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use super::error::TorchFfiError;

#[cfg(feature = "pytorch")]
use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};

#[cfg(feature = "pytorch")]
use crate::value::torch::{rt_torch_free, rt_torch_grad, rt_torch_zero_grad};

// ============================================================================
// Optimizer State
// ============================================================================

#[cfg(feature = "pytorch")]
#[derive(Debug)]
struct OptimizerState {
    params: Vec<u64>,  // Parameter tensor handles
    lr: f64,
    optimizer_type: OptimizerType,
}

#[cfg(feature = "pytorch")]
#[derive(Debug)]
enum OptimizerType {
    SGD {
        momentum: f64,
        weight_decay: f64,
        velocity: Vec<Option<u64>>,  // Momentum buffers (one per param)
    },
    Adam {
        beta1: f64,
        beta2: f64,
        eps: f64,
        weight_decay: f64,
        m: Vec<Option<u64>>,  // First moment estimates
        v: Vec<Option<u64>>,  // Second moment estimates
        step: usize,
    },
    AdamW {
        beta1: f64,
        beta2: f64,
        eps: f64,
        weight_decay: f64,
        m: Vec<Option<u64>>,  // First moment estimates
        v: Vec<Option<u64>>,  // Second moment estimates
        step: usize,
    },
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    pub(crate) static ref OPTIMIZER_REGISTRY: Mutex<HashMap<u64, Arc<OptimizerState>>> =
        Mutex::new(HashMap::new());
    static ref NEXT_OPTIMIZER_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "pytorch")]
fn next_optimizer_handle() -> u64 {
    NEXT_OPTIMIZER_HANDLE.fetch_add(1, Ordering::SeqCst)
}

/// Helper function to create an optimizer with common validation and registration logic
#[cfg(feature = "pytorch")]
fn create_optimizer<F>(
    params_ptr: *const u64,
    num_params: usize,
    lr: f64,
    create_type: F,
) -> u64
where
    F: FnOnce(usize) -> OptimizerType,
{
    if params_ptr.is_null() || num_params == 0 {
        return 0;
    }

    let params = unsafe { std::slice::from_raw_parts(params_ptr, num_params) }.to_vec();

    // Verify all parameter handles are valid
    let registry = TENSOR_REGISTRY.lock();
    for &param_handle in &params {
        if !registry.contains_key(&param_handle) {
            return 0;
        }
    }
    drop(registry);

    let optimizer_type = create_type(num_params);

    let state = OptimizerState {
        params,
        lr,
        optimizer_type,
    };

    let handle = next_optimizer_handle();
    OPTIMIZER_REGISTRY
        .lock()
        .insert(handle, Arc::new(state));

    handle
}

// ============================================================================
// SGD Optimizer
// ============================================================================

/// Create SGD optimizer
/// params_ptr: pointer to array of tensor handles
/// num_params: number of parameters
/// lr: learning rate
/// momentum: momentum factor (0.0 for no momentum)
/// weight_decay: L2 penalty (0.0 for no weight decay)
#[no_mangle]
pub extern "C" fn rt_torch_sgd_new(
    params_ptr: *const u64,
    num_params: usize,
    lr: f64,
    momentum: f64,
    weight_decay: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let handle = create_optimizer(params_ptr, num_params, lr, |n| {
            OptimizerType::SGD {
                momentum,
                weight_decay,
                velocity: vec![None; n],
            }
        });

        if handle != 0 {
            tracing::debug!(
                "rt_torch_sgd_new: handle={} num_params={} lr={} momentum={} weight_decay={}",
                handle,
                num_params,
                lr,
                momentum,
                weight_decay
            );
        }
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (params_ptr, num_params, lr, momentum, weight_decay);
        0
    }
}

// ============================================================================
// Adam Optimizer
// ============================================================================

/// Create Adam optimizer
#[no_mangle]
pub extern "C" fn rt_torch_adam_new(
    params_ptr: *const u64,
    num_params: usize,
    lr: f64,
    beta1: f64,
    beta2: f64,
    eps: f64,
    weight_decay: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let handle = create_optimizer(params_ptr, num_params, lr, |n| {
            OptimizerType::Adam {
                beta1,
                beta2,
                eps,
                weight_decay,
                m: vec![None; n],
                v: vec![None; n],
                step: 0,
            }
        });

        if handle != 0 {
            tracing::debug!(
                "rt_torch_adam_new: handle={} num_params={} lr={} beta1={} beta2={} eps={} weight_decay={}",
                handle,
                num_params,
                lr,
                beta1,
                beta2,
                eps,
                weight_decay
            );
        }
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (params_ptr, num_params, lr, beta1, beta2, eps, weight_decay);
        0
    }
}

// ============================================================================
// AdamW Optimizer
// ============================================================================

/// Create AdamW optimizer (Adam with decoupled weight decay)
#[no_mangle]
pub extern "C" fn rt_torch_adamw_new(
    params_ptr: *const u64,
    num_params: usize,
    lr: f64,
    beta1: f64,
    beta2: f64,
    eps: f64,
    weight_decay: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let handle = create_optimizer(params_ptr, num_params, lr, |n| {
            OptimizerType::AdamW {
                beta1,
                beta2,
                eps,
                weight_decay,
                m: vec![None; n],
                v: vec![None; n],
                step: 0,
            }
        });

        if handle != 0 {
            tracing::debug!(
                "rt_torch_adamw_new: handle={} num_params={} lr={} beta1={} beta2={} eps={} weight_decay={}",
                handle,
                num_params,
                lr,
                beta1,
                beta2,
                eps,
                weight_decay
            );
        }
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (params_ptr, num_params, lr, beta1, beta2, eps, weight_decay);
        0
    }
}

// ============================================================================
// Optimizer Step
// ============================================================================

/// Perform one optimization step (update parameters using gradients)
#[no_mangle]
pub extern "C" fn rt_torch_optimizer_step(optimizer_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        let Some(opt_state) = opt_registry.get(&optimizer_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(opt_registry);

        match &opt_state.optimizer_type {
            OptimizerType::SGD {
                momentum,
                weight_decay,
                velocity,
            } => {
                let lr = opt_state.lr;
                let mom = *momentum;
                let wd = *weight_decay;

                // Clone velocity before iteration
                let mut new_velocity = velocity.clone();

                for (i, &param_handle) in opt_state.params.iter().enumerate() {
                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(param) = tensor_registry.get(&param_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // Get gradient
                    let grad_handle = rt_torch_grad(param_handle);
                    if grad_handle == 0 {
                        continue; // No gradient for this parameter
                    }

                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(grad) = tensor_registry.get(&grad_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // Apply weight decay: grad = grad + weight_decay * param
                    let mut d_p = if wd != 0.0 {
                        &grad.0 + &param.0 * wd
                    } else {
                        grad.0.shallow_clone()
                    };

                    // Apply momentum
                    if mom != 0.0 {
                        if let Some(vel_handle) = new_velocity[i] {
                            let tensor_registry = TENSOR_REGISTRY.lock();
                            let Some(vel) = tensor_registry.get(&vel_handle).cloned() else {
                                continue;
                            };
                            drop(tensor_registry);

                            // velocity = momentum * velocity + grad
                            let new_vel = &vel.0 * mom + &d_p;
                            let new_vel_handle = next_handle();
                            TENSOR_REGISTRY
                                .lock()
                                .insert(new_vel_handle, Arc::new(TensorWrapper(new_vel.shallow_clone())));
                            new_velocity[i] = Some(new_vel_handle);
                            d_p = new_vel;
                        } else {
                            // Initialize velocity with gradient
                            let vel_handle = next_handle();
                            TENSOR_REGISTRY
                                .lock()
                                .insert(vel_handle, Arc::new(TensorWrapper(d_p.shallow_clone())));
                            new_velocity[i] = Some(vel_handle);
                        }
                    }

                    // Update parameter: param = param - lr * d_p
                    let new_param = &param.0 - &d_p * lr;
                    TENSOR_REGISTRY
                        .lock()
                        .insert(param_handle, Arc::new(TensorWrapper(new_param)));

                    // Free gradient handle
                    rt_torch_free(grad_handle);
                }

                // Update optimizer state with new velocity
                if mom != 0.0 {
                    let mut opt_registry = OPTIMIZER_REGISTRY.lock();
                    if let Some(state) = opt_registry.get_mut(&optimizer_handle) {
                        // Create new state with updated velocity
                        let new_state = OptimizerState {
                            params: opt_state.params.clone(),
                            lr: opt_state.lr,
                            optimizer_type: OptimizerType::SGD {
                                momentum: mom,
                                weight_decay: wd,
                                velocity: new_velocity,
                            },
                        };
                        *state = Arc::new(new_state);
                    }
                }

                tracing::debug!("rt_torch_optimizer_step: SGD optimizer={}", optimizer_handle);
                TorchFfiError::Success as i32
            }
            OptimizerType::Adam {
                beta1,
                beta2,
                eps,
                weight_decay,
                m,
                v,
                step,
            } => {
                let lr = opt_state.lr;
                let b1 = *beta1;
                let b2 = *beta2;
                let epsilon = *eps;
                let wd = *weight_decay;
                let current_step = *step + 1;

                let mut new_m = m.clone();
                let mut new_v = v.clone();

                for (i, &param_handle) in opt_state.params.iter().enumerate() {
                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(param) = tensor_registry.get(&param_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // Get gradient
                    let grad_handle = rt_torch_grad(param_handle);
                    if grad_handle == 0 {
                        continue;
                    }

                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(grad) = tensor_registry.get(&grad_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // Apply weight decay: grad = grad + weight_decay * param
                    let grad_with_wd = if wd != 0.0 {
                        &grad.0 + &param.0 * wd
                    } else {
                        grad.0.shallow_clone()
                    };

                    // Update biased first moment estimate: m = beta1 * m + (1 - beta1) * grad
                    let new_m_i = if let Some(m_handle) = new_m[i] {
                        let tensor_registry = TENSOR_REGISTRY.lock();
                        let Some(m_tensor) = tensor_registry.get(&m_handle).cloned() else {
                            continue;
                        };
                        drop(tensor_registry);
                        &m_tensor.0 * b1 + &grad_with_wd * (1.0 - b1)
                    } else {
                        &grad_with_wd * (1.0 - b1)
                    };

                    // Update biased second moment estimate: v = beta2 * v + (1 - beta2) * grad^2
                    let grad_sq = &grad_with_wd * &grad_with_wd;
                    let new_v_i = if let Some(v_handle) = new_v[i] {
                        let tensor_registry = TENSOR_REGISTRY.lock();
                        let Some(v_tensor) = tensor_registry.get(&v_handle).cloned() else {
                            continue;
                        };
                        drop(tensor_registry);
                        &v_tensor.0 * b2 + &grad_sq * (1.0 - b2)
                    } else {
                        &grad_sq * (1.0 - b2)
                    };

                    // Bias correction
                    let bias_correction1 = 1.0 - b1.powi(current_step as i32);
                    let bias_correction2 = 1.0 - b2.powi(current_step as i32);

                    // Compute step size: lr * sqrt(1 - beta2^t) / (1 - beta1^t)
                    let step_size = lr * (bias_correction2.sqrt() / bias_correction1);

                    // Update parameter: param = param - step_size * m / (sqrt(v) + eps)
                    let denom = new_v_i.sqrt() + epsilon;
                    let new_param = &param.0 - (&new_m_i / &denom) * step_size;

                    // Store updated parameter
                    TENSOR_REGISTRY
                        .lock()
                        .insert(param_handle, Arc::new(TensorWrapper(new_param)));

                    // Store updated moments
                    let m_handle = next_handle();
                    TENSOR_REGISTRY
                        .lock()
                        .insert(m_handle, Arc::new(TensorWrapper(new_m_i)));
                    new_m[i] = Some(m_handle);

                    let v_handle = next_handle();
                    TENSOR_REGISTRY
                        .lock()
                        .insert(v_handle, Arc::new(TensorWrapper(new_v_i)));
                    new_v[i] = Some(v_handle);

                    // Free gradient handle
                    rt_torch_free(grad_handle);
                }

                // Update optimizer state
                let mut opt_registry = OPTIMIZER_REGISTRY.lock();
                if let Some(state) = opt_registry.get_mut(&optimizer_handle) {
                    let new_state = OptimizerState {
                        params: opt_state.params.clone(),
                        lr: opt_state.lr,
                        optimizer_type: OptimizerType::Adam {
                            beta1: b1,
                            beta2: b2,
                            eps: epsilon,
                            weight_decay: wd,
                            m: new_m,
                            v: new_v,
                            step: current_step,
                        },
                    };
                    *state = Arc::new(new_state);
                }

                tracing::debug!("rt_torch_optimizer_step: Adam optimizer={} step={}", optimizer_handle, current_step);
                TorchFfiError::Success as i32
            }
            OptimizerType::AdamW {
                beta1,
                beta2,
                eps,
                weight_decay,
                m,
                v,
                step,
            } => {
                let lr = opt_state.lr;
                let b1 = *beta1;
                let b2 = *beta2;
                let epsilon = *eps;
                let wd = *weight_decay;
                let current_step = *step + 1;

                let mut new_m = m.clone();
                let mut new_v = v.clone();

                for (i, &param_handle) in opt_state.params.iter().enumerate() {
                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(param) = tensor_registry.get(&param_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // Get gradient
                    let grad_handle = rt_torch_grad(param_handle);
                    if grad_handle == 0 {
                        continue;
                    }

                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(grad) = tensor_registry.get(&grad_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // AdamW: Apply decoupled weight decay directly to parameter
                    // (not to gradient like Adam)

                    // Update biased first moment estimate: m = beta1 * m + (1 - beta1) * grad
                    let new_m_i = if let Some(m_handle) = new_m[i] {
                        let tensor_registry = TENSOR_REGISTRY.lock();
                        let Some(m_tensor) = tensor_registry.get(&m_handle).cloned() else {
                            continue;
                        };
                        drop(tensor_registry);
                        &m_tensor.0 * b1 + &grad.0 * (1.0 - b1)
                    } else {
                        &grad.0 * (1.0 - b1)
                    };

                    // Update biased second moment estimate: v = beta2 * v + (1 - beta2) * grad^2
                    let grad_sq = &grad.0 * &grad.0;
                    let new_v_i = if let Some(v_handle) = new_v[i] {
                        let tensor_registry = TENSOR_REGISTRY.lock();
                        let Some(v_tensor) = tensor_registry.get(&v_handle).cloned() else {
                            continue;
                        };
                        drop(tensor_registry);
                        &v_tensor.0 * b2 + &grad_sq * (1.0 - b2)
                    } else {
                        &grad_sq * (1.0 - b2)
                    };

                    // Bias correction
                    let bias_correction1 = 1.0 - b1.powi(current_step as i32);
                    let bias_correction2 = 1.0 - b2.powi(current_step as i32);

                    // Compute step size
                    let step_size = lr * (bias_correction2.sqrt() / bias_correction1);

                    // Update parameter: param = param - step_size * m / (sqrt(v) + eps) - lr * weight_decay * param
                    let denom = new_v_i.sqrt() + epsilon;
                    let mut new_param = &param.0 - (&new_m_i / &denom) * step_size;

                    // AdamW: Decoupled weight decay
                    if wd != 0.0 {
                        new_param = &new_param - &param.0 * (lr * wd);
                    }

                    // Store updated parameter
                    TENSOR_REGISTRY
                        .lock()
                        .insert(param_handle, Arc::new(TensorWrapper(new_param)));

                    // Store updated moments
                    let m_handle = next_handle();
                    TENSOR_REGISTRY
                        .lock()
                        .insert(m_handle, Arc::new(TensorWrapper(new_m_i)));
                    new_m[i] = Some(m_handle);

                    let v_handle = next_handle();
                    TENSOR_REGISTRY
                        .lock()
                        .insert(v_handle, Arc::new(TensorWrapper(new_v_i)));
                    new_v[i] = Some(v_handle);

                    // Free gradient handle
                    rt_torch_free(grad_handle);
                }

                // Update optimizer state
                let mut opt_registry = OPTIMIZER_REGISTRY.lock();
                if let Some(state) = opt_registry.get_mut(&optimizer_handle) {
                    let new_state = OptimizerState {
                        params: opt_state.params.clone(),
                        lr: opt_state.lr,
                        optimizer_type: OptimizerType::AdamW {
                            beta1: b1,
                            beta2: b2,
                            eps: epsilon,
                            weight_decay: wd,
                            m: new_m,
                            v: new_v,
                            step: current_step,
                        },
                    };
                    *state = Arc::new(new_state);
                }

                tracing::debug!("rt_torch_optimizer_step: AdamW optimizer={} step={}", optimizer_handle, current_step);
                TorchFfiError::Success as i32
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = optimizer_handle;
        TorchFfiError::NotAvailable as i32
    }
}

// ============================================================================
// Optimizer Utilities
// ============================================================================

/// Zero all gradients for parameters tracked by optimizer
#[no_mangle]
pub extern "C" fn rt_torch_optimizer_zero_grad(optimizer_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        let Some(opt_state) = opt_registry.get(&optimizer_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(opt_registry);

        for &param_handle in &opt_state.params {
            // Call rt_torch_zero_grad for each parameter
            let _ = rt_torch_zero_grad(param_handle);
        }

        tracing::debug!(
            "rt_torch_optimizer_zero_grad: optimizer={} params={}",
            optimizer_handle,
            opt_state.params.len()
        );
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = optimizer_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Get current learning rate
#[no_mangle]
pub extern "C" fn rt_torch_optimizer_get_lr(optimizer_handle: u64) -> f64 {
    #[cfg(feature = "pytorch")]
    {
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        let Some(opt_state) = opt_registry.get(&optimizer_handle) else {
            return 0.0;
        };
        let lr = opt_state.lr;
        drop(opt_registry);

        tracing::debug!("rt_torch_optimizer_get_lr: optimizer={} lr={}", optimizer_handle, lr);
        lr
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = optimizer_handle;
        0.0
    }
}

/// Set learning rate
#[no_mangle]
pub extern "C" fn rt_torch_optimizer_set_lr(optimizer_handle: u64, new_lr: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let mut opt_registry = OPTIMIZER_REGISTRY.lock();
        let Some(opt_state) = opt_registry.get_mut(&optimizer_handle) else {
            return TorchFfiError::InvalidHandle as i32;
        };

        // Create new state with updated learning rate
        let new_state = OptimizerState {
            params: opt_state.params.clone(),
            lr: new_lr,
            optimizer_type: match &opt_state.optimizer_type {
                OptimizerType::SGD { momentum, weight_decay, velocity } => {
                    OptimizerType::SGD {
                        momentum: *momentum,
                        weight_decay: *weight_decay,
                        velocity: velocity.clone(),
                    }
                }
                OptimizerType::Adam { beta1, beta2, eps, weight_decay, m, v, step } => {
                    OptimizerType::Adam {
                        beta1: *beta1,
                        beta2: *beta2,
                        eps: *eps,
                        weight_decay: *weight_decay,
                        m: m.clone(),
                        v: v.clone(),
                        step: *step,
                    }
                }
                OptimizerType::AdamW { beta1, beta2, eps, weight_decay, m, v, step } => {
                    OptimizerType::AdamW {
                        beta1: *beta1,
                        beta2: *beta2,
                        eps: *eps,
                        weight_decay: *weight_decay,
                        m: m.clone(),
                        v: v.clone(),
                        step: *step,
                    }
                }
            },
        };

        *opt_state = Arc::new(new_state);

        tracing::debug!(
            "rt_torch_optimizer_set_lr: optimizer={} new_lr={}",
            optimizer_handle,
            new_lr
        );
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (optimizer_handle, new_lr);
        TorchFfiError::NotAvailable as i32
    }
}

/// Free optimizer and its resources
#[no_mangle]
pub extern "C" fn rt_torch_optimizer_free(optimizer_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let mut opt_registry = OPTIMIZER_REGISTRY.lock();
        if opt_registry.remove(&optimizer_handle).is_some() {
            tracing::debug!("rt_torch_optimizer_free: freed optimizer={}", optimizer_handle);
            TorchFfiError::Success as i32
        } else {
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = optimizer_handle;
        TorchFfiError::NotAvailable as i32
    }
}
