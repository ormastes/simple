//! Fast Fourier Transform operations for PyTorch tensors
//!
//! Simple Math #1950-#1959: FFT Operations
//! Provides FFI functions for frequency domain operations:
//! - fft: 1D Fast Fourier Transform
//! - ifft: 1D Inverse Fast Fourier Transform
//! - rfft: 1D Real FFT (for real-valued inputs)
//! - irfft: 1D Inverse Real FFT
//! - fftn: N-D Fast Fourier Transform
//! - fftshift: Shift zero-frequency to center
//! - ifftshift: Inverse fftshift

use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use tch::Tensor;

// ============================================================================
// Simple Math: FFT Operations (#1950-#1959)
// ============================================================================

/// 1D Fast Fourier Transform
/// Simple Math #1950-#1959: Complex FFT
/// Returns handle to frequency-domain tensor, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_fft(tensor_handle: u64, n: i64, dim: i64, norm: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        // norm: 0 = None, 1 = "forward", 2 = "backward", 3 = "ortho"
        let norm_str = match norm {
            1 => Some("forward"),
            2 => Some("backward"),
            3 => Some("ortho"),
            _ => None,
        };

        let n_opt = if n > 0 { Some(n) } else { None };
        let result = tensor.0.fft_fft(n_opt, dim, norm_str);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_fft: {} n={} dim={} norm={} -> handle={}",
            tensor_handle,
            n,
            dim,
            norm,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, n, dim, norm);
        0
    }
}

/// 1D Inverse Fast Fourier Transform
/// Simple Math #1950-#1959: Complex IFFT
/// Returns handle to time-domain tensor, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_ifft(tensor_handle: u64, n: i64, dim: i64, norm: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let norm_str = match norm {
            1 => Some("forward"),
            2 => Some("backward"),
            3 => Some("ortho"),
            _ => None,
        };

        let n_opt = if n > 0 { Some(n) } else { None };
        let result = tensor.0.fft_ifft(n_opt, dim, norm_str);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_ifft: {} n={} dim={} norm={} -> handle={}",
            tensor_handle,
            n,
            dim,
            norm,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, n, dim, norm);
        0
    }
}

/// 1D Real FFT (for real-valued inputs)
/// Simple Math #1950-#1959: Real-to-complex FFT
/// Returns handle to complex frequency-domain tensor, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_rfft(tensor_handle: u64, n: i64, dim: i64, norm: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let norm_str = match norm {
            1 => Some("forward"),
            2 => Some("backward"),
            3 => Some("ortho"),
            _ => None,
        };

        let n_opt = if n > 0 { Some(n) } else { None };
        let result = tensor.0.fft_rfft(n_opt, dim, norm_str);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_rfft: {} n={} dim={} norm={} -> handle={}",
            tensor_handle,
            n,
            dim,
            norm,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, n, dim, norm);
        0
    }
}

/// 1D Inverse Real FFT
/// Simple Math #1950-#1959: Complex-to-real IFFT
/// Returns handle to real time-domain tensor, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_irfft(tensor_handle: u64, n: i64, dim: i64, norm: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let norm_str = match norm {
            1 => Some("forward"),
            2 => Some("backward"),
            3 => Some("ortho"),
            _ => None,
        };

        let n_opt = if n > 0 { Some(n) } else { None };
        let result = tensor.0.fft_irfft(n_opt, dim, norm_str);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_irfft: {} n={} dim={} norm={} -> handle={}",
            tensor_handle,
            n,
            dim,
            norm,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, n, dim, norm);
        0
    }
}

/// N-D Fast Fourier Transform
/// Simple Math #1950-#1959: Multi-dimensional FFT
/// dims_ptr: dimensions to transform, ndim: number of dimensions
/// Returns handle to N-D frequency-domain tensor, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_fftn(tensor_handle: u64, dims_ptr: *const i64, ndim: i32, norm: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let dims = if ndim > 0 {
            unsafe { std::slice::from_raw_parts(dims_ptr, ndim as usize) }
        } else {
            &[]
        };

        let norm_str = match norm {
            1 => Some("forward"),
            2 => Some("backward"),
            3 => Some("ortho"),
            _ => None,
        };

        let dims_vec: Vec<i64> = dims.to_vec();
        let result = tensor.0.fft_fftn(Some(&dims_vec), None, norm_str);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_fftn: {} dims={:?} norm={} -> handle={}",
            tensor_handle,
            dims,
            norm,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dims_ptr, ndim, norm);
        0
    }
}

/// Shift zero-frequency component to center of spectrum
/// Simple Math #1950-#1959: FFT frequency shift
/// dim: dimension to shift, or -1 for all dimensions
/// Returns handle to shifted tensor, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_fftshift(tensor_handle: u64, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = if dim == -1 {
            tensor.0.fft_fftshift(None::<&[i64]>)
        } else {
            let dims = vec![dim];
            tensor.0.fft_fftshift(Some(dims.as_slice()))
        };
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_fftshift: {} dim={} -> handle={}", tensor_handle, dim, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim);
        0
    }
}

/// Inverse of fftshift
/// Simple Math #1950-#1959: Inverse FFT frequency shift
/// dim: dimension to shift, or -1 for all dimensions
/// Returns handle to shifted tensor, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_ifftshift(tensor_handle: u64, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = if dim == -1 {
            tensor.0.fft_ifftshift(None::<&[i64]>)
        } else {
            let dims = vec![dim];
            tensor.0.fft_ifftshift(Some(dims.as_slice()))
        };
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_ifftshift: {} dim={} -> handle={}", tensor_handle, dim, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim);
        0
    }
}
