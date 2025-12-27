//! Learning rate schedulers for training optimization

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
use super::optimizer::OPTIMIZER_REGISTRY;

#[cfg(feature = "pytorch")]
use crate::value::torch::{rt_torch_optimizer_get_lr, rt_torch_optimizer_set_lr};

// ============================================================================
// Week 9: Learning Rate Schedulers (StepLR, ExponentialLR, CosineAnnealingLR)
// ============================================================================

#[cfg(feature = "pytorch")]
#[derive(Debug)]
enum SchedulerState {
    StepLR {
        optimizer: u64,
        step_size: usize,
        gamma: f64,
        last_epoch: usize,
    },
    ExponentialLR {
        optimizer: u64,
        gamma: f64,
        last_epoch: usize,
    },
    CosineAnnealingLR {
        optimizer: u64,
        t_max: usize,
        eta_min: f64,
        last_epoch: usize,
        base_lr: f64,
    },
    ReduceLROnPlateau {
        optimizer: u64,
        mode: i32,  // 0=min, 1=max
        factor: f64,
        patience: usize,
        threshold: f64,
        cooldown: usize,
        min_lr: f64,
        num_bad_epochs: usize,
        cooldown_counter: usize,
        best: f64,
    },
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref SCHEDULER_REGISTRY: Mutex<HashMap<u64, Arc<Mutex<SchedulerState>>>> =
        Mutex::new(HashMap::new());
    static ref NEXT_SCHEDULER_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "pytorch")]
fn next_scheduler_handle() -> u64 {
    NEXT_SCHEDULER_HANDLE.fetch_add(1, Ordering::SeqCst)
}

/// Create StepLR scheduler
/// Decays the learning rate by gamma every step_size epochs
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_step_new(
    optimizer_handle: u64,
    step_size: usize,
    gamma: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if step_size == 0 {
            return 0;
        }

        // Verify optimizer exists
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        if !opt_registry.contains_key(&optimizer_handle) {
            return 0;
        }
        drop(opt_registry);

        let state = SchedulerState::StepLR {
            optimizer: optimizer_handle,
            step_size,
            gamma,
            last_epoch: 0,
        };

        let handle = next_scheduler_handle();
        SCHEDULER_REGISTRY
            .lock()
            .insert(handle, Arc::new(Mutex::new(state)));

        tracing::debug!(
            "rt_torch_scheduler_step_new: handle={} optimizer={} step_size={} gamma={}",
            handle,
            optimizer_handle,
            step_size,
            gamma
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (optimizer_handle, step_size, gamma);
        0
    }
}

/// Create ExponentialLR scheduler
/// Decays the learning rate by gamma every epoch
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_exponential_new(optimizer_handle: u64, gamma: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        if !opt_registry.contains_key(&optimizer_handle) {
            return 0;
        }
        drop(opt_registry);

        let state = SchedulerState::ExponentialLR {
            optimizer: optimizer_handle,
            gamma,
            last_epoch: 0,
        };

        let handle = next_scheduler_handle();
        SCHEDULER_REGISTRY
            .lock()
            .insert(handle, Arc::new(Mutex::new(state)));

        tracing::debug!(
            "rt_torch_scheduler_exponential_new: handle={} optimizer={} gamma={}",
            handle,
            optimizer_handle,
            gamma
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (optimizer_handle, gamma);
        0
    }
}

/// Create CosineAnnealingLR scheduler
/// Anneals the learning rate using a cosine schedule
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_cosine_new(
    optimizer_handle: u64,
    t_max: usize,
    eta_min: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if t_max == 0 {
            return 0;
        }

        let opt_registry = OPTIMIZER_REGISTRY.lock();
        let Some(opt) = opt_registry.get(&optimizer_handle) else {
            return 0;
        };
        let base_lr = opt.lr;
        drop(opt_registry);

        let state = SchedulerState::CosineAnnealingLR {
            optimizer: optimizer_handle,
            t_max,
            eta_min,
            last_epoch: 0,
            base_lr,
        };

        let handle = next_scheduler_handle();
        SCHEDULER_REGISTRY
            .lock()
            .insert(handle, Arc::new(Mutex::new(state)));

        tracing::debug!(
            "rt_torch_scheduler_cosine_new: handle={} optimizer={} t_max={} eta_min={}",
            handle,
            optimizer_handle,
            t_max,
            eta_min
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (optimizer_handle, t_max, eta_min);
        0
    }
}

/// Create ReduceLROnPlateau scheduler
/// Reduces learning rate when a metric has stopped improving
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_plateau_new(
    optimizer_handle: u64,
    mode: i32,
    factor: f64,
    patience: usize,
    threshold: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        if !opt_registry.contains_key(&optimizer_handle) {
            return 0;
        }
        drop(opt_registry);

        let best = if mode == 0 {
            f64::INFINITY
        } else {
            f64::NEG_INFINITY
        };

        let state = SchedulerState::ReduceLROnPlateau {
            optimizer: optimizer_handle,
            mode,
            factor,
            patience,
            threshold,
            cooldown: 0,
            min_lr: 0.0,
            num_bad_epochs: 0,
            cooldown_counter: 0,
            best,
        };

        let handle = next_scheduler_handle();
        SCHEDULER_REGISTRY
            .lock()
            .insert(handle, Arc::new(Mutex::new(state)));

        tracing::debug!(
            "rt_torch_scheduler_plateau_new: handle={} optimizer={} mode={} factor={} patience={}",
            handle,
            optimizer_handle,
            mode,
            factor,
            patience
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (optimizer_handle, mode, factor, patience, threshold);
        0
    }
}

/// Step the scheduler (for epoch-based schedulers)
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_step(scheduler_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let sched_registry = SCHEDULER_REGISTRY.lock();
        let Some(sched) = sched_registry.get(&scheduler_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(sched_registry);

        let mut state = sched.lock();

        match &mut *state {
            SchedulerState::StepLR {
                optimizer,
                step_size,
                gamma,
                last_epoch,
            } => {
                *last_epoch += 1;

                if *last_epoch % *step_size == 0 {
                    // Get current LR
                    let current_lr = rt_torch_optimizer_get_lr(*optimizer);
                    let new_lr = current_lr * *gamma;

                    // Set new LR
                    let _ = rt_torch_optimizer_set_lr(*optimizer, new_lr);

                    tracing::debug!(
                        "rt_torch_scheduler_step: StepLR scheduler={} epoch={} lr={} -> {}",
                        scheduler_handle,
                        last_epoch,
                        current_lr,
                        new_lr
                    );
                }

                TorchFfiError::Success as i32
            }
            SchedulerState::ExponentialLR {
                optimizer,
                gamma,
                last_epoch,
            } => {
                *last_epoch += 1;

                let current_lr = rt_torch_optimizer_get_lr(*optimizer);
                let new_lr = current_lr * *gamma;

                let _ = rt_torch_optimizer_set_lr(*optimizer, new_lr);

                tracing::debug!(
                    "rt_torch_scheduler_step: ExponentialLR scheduler={} epoch={} lr={} -> {}",
                    scheduler_handle,
                    last_epoch,
                    current_lr,
                    new_lr
                );

                TorchFfiError::Success as i32
            }
            SchedulerState::CosineAnnealingLR {
                optimizer,
                t_max,
                eta_min,
                last_epoch,
                base_lr,
            } => {
                *last_epoch += 1;

                let cos_arg = std::f64::consts::PI * (*last_epoch as f64) / (*t_max as f64);
                let new_lr = *eta_min + (*base_lr - *eta_min) * (1.0 + cos_arg.cos()) / 2.0;

                let _ = rt_torch_optimizer_set_lr(*optimizer, new_lr);

                tracing::debug!(
                    "rt_torch_scheduler_step: CosineAnnealingLR scheduler={} epoch={}/{} lr={}",
                    scheduler_handle,
                    last_epoch,
                    t_max,
                    new_lr
                );

                TorchFfiError::Success as i32
            }
            SchedulerState::ReduceLROnPlateau { .. } => {
                // ReduceLROnPlateau requires metric, use step_with_metric instead
                TorchFfiError::InvalidParameter as i32
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = scheduler_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Step the scheduler with a metric (for ReduceLROnPlateau)
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_step_with_metric(scheduler_handle: u64, metric: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let sched_registry = SCHEDULER_REGISTRY.lock();
        let Some(sched) = sched_registry.get(&scheduler_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(sched_registry);

        let mut state = sched.lock();

        match &mut *state {
            SchedulerState::ReduceLROnPlateau {
                optimizer,
                mode,
                factor,
                patience,
                threshold,
                cooldown_counter,
                num_bad_epochs,
                best,
                min_lr,
                ..
            } => {
                if *cooldown_counter > 0 {
                    *cooldown_counter -= 1;
                    *num_bad_epochs = 0;
                }

                let is_better = if *mode == 0 {
                    // min mode
                    metric < *best - *threshold
                } else {
                    // max mode
                    metric > *best + *threshold
                };

                if is_better {
                    *best = metric;
                    *num_bad_epochs = 0;
                } else {
                    *num_bad_epochs += 1;
                }

                if *num_bad_epochs >= *patience && *cooldown_counter == 0 {
                    let current_lr = rt_torch_optimizer_get_lr(*optimizer);
                    let new_lr = (current_lr * *factor).max(*min_lr);

                    if new_lr != current_lr {
                        let _ = rt_torch_optimizer_set_lr(*optimizer, new_lr);
                        *cooldown_counter = 0;
                        *num_bad_epochs = 0;

                        tracing::debug!(
                            "rt_torch_scheduler_step_with_metric: ReduceLROnPlateau scheduler={} metric={} lr={} -> {}",
                            scheduler_handle,
                            metric,
                            current_lr,
                            new_lr
                        );
                    }
                }

                TorchFfiError::Success as i32
            }
            _ => {
                // Other schedulers don't need metric
                rt_torch_scheduler_step(scheduler_handle)
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (scheduler_handle, metric);
        TorchFfiError::NotAvailable as i32
    }
}

/// Free a scheduler
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_free(scheduler_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let mut sched_registry = SCHEDULER_REGISTRY.lock();
        if sched_registry.remove(&scheduler_handle).is_some() {
            tracing::debug!("rt_torch_scheduler_free: freed scheduler={}", scheduler_handle);
            TorchFfiError::Success as i32
        } else {
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = scheduler_handle;
        TorchFfiError::NotAvailable as i32
    }
}
