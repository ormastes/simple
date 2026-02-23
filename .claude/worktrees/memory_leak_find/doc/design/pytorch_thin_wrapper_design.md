# PyTorch Thin Rust Wrapper Design

**Status**: Design
**Created**: 2026-02-08
**Updated**: 2026-02-08

## Overview

Design for a minimal Rust FFI wrapper around PyTorch's libtorch C++ library, following the three-tier SFFI pattern.

## Goals

1. **Minimal Rust code**: Only what's needed for FFI safety
2. **Thin wrapper**: No business logic, just C FFI bindings
3. **Memory safe**: Proper lifetime management
4. **Cross-platform**: Linux, macOS, Windows support
5. **CUDA support**: Optional GPU acceleration

## PyTorch C++ API Surface

### Core Types

- `torch::Tensor` - Core tensor type
- `torch::Device` - CPU/CUDA device
- `torch::Dtype` - Data type (float32, int64, etc.)
- `torch::nn::Module` - Base class for neural network modules

### Key Operations

**Tensor Creation:**
- `torch::zeros(shape, options)` - Zero tensor
- `torch::ones(shape, options)` - Ones tensor
- `torch::randn(shape, options)` - Random normal
- `torch::from_blob(data, shape)` - From raw data

**Tensor Operations:**
- `tensor.add(other)` - Addition
- `tensor.mul(other)` - Multiplication
- `tensor.matmul(other)` - Matrix multiplication
- `tensor.transpose(dim0, dim1)` - Transpose

**Activations:**
- `torch::relu(tensor)` - ReLU activation
- `torch::sigmoid(tensor)` - Sigmoid activation
- `torch::tanh(tensor)` - Tanh activation

**Device Management:**
- `tensor.to(device)` - Move to device
- `tensor.cuda()` - Move to CUDA
- `tensor.cpu()` - Move to CPU

## Architecture

```
┌──────────────────────────────────────────────┐
│ Simple User Code (Tier 3)                   │
│   use lib.torch.*                           │
│   val t = Tensor.zeros([2, 3])              │
└──────────────┬───────────────────────────────┘
               │
               ▼
┌──────────────────────────────────────────────┐
│ SFFI Bindings (Tier 2)                      │
│   src/lib/torch/ffi.spl                     │
│   extern fn rt_torch_tensor_zeros(...)      │
└──────────────┬───────────────────────────────┘
               │
               ▼
┌──────────────────────────────────────────────┐
│ Rust FFI Wrapper (Tier 1)                   │
│   .build/rust/ffi_torch/src/lib.rs          │
│   #[no_mangle] pub extern "C"               │
│   fn simple_torch_tensor_zeros(...)         │
└──────────────┬───────────────────────────────┘
               │
               ▼
┌──────────────────────────────────────────────┐
│ LibTorch C++ (Tier 0)                       │
│   /usr/local/lib/libtorch.so                │
│   torch::zeros(...), torch::Tensor          │
└──────────────────────────────────────────────┘
```

## Tier 1: Rust FFI Wrapper Implementation

### Directory Structure

```
.build/rust/ffi_torch/
├── Cargo.toml           # Package manifest
├── build.rs             # Build script (find libtorch)
├── README.md            # Setup instructions
└── src/
    ├── lib.rs           # Main entry point
    ├── tensor.rs        # Tensor operations
    ├── nn.rs            # Neural network modules
    └── device.rs        # Device management
```

### Cargo.toml

```toml
[package]
name = "simple-torch-ffi"
version = "0.1.0"
edition = "2021"
description = "Thin Rust FFI wrapper for PyTorch libtorch"
license = "MIT OR Apache-2.0"

[lib]
name = "simple_torch_ffi"
crate-type = ["cdylib"]  # Dynamic library for Simple runtime

[dependencies]
libc = "0.2"

[build-dependencies]
pkg-config = "0.3"
cc = "1.0"

[package.metadata.simple]
# Simple build system metadata
library = "torch"
system-deps = ["libtorch >= 2.0"]
platforms = ["linux", "macos", "windows"]
optional-deps = ["cuda >= 11.8"]
```

### build.rs - Build Script

```rust
// .build/rust/ffi_torch/build.rs

use std::env;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    // Try to find libtorch via environment variable
    if let Ok(torch_path) = env::var("LIBTORCH") {
        println!("cargo:rustc-link-search=native={}/lib", torch_path);
    } else if let Ok(torch_path) = env::var("TORCH_HOME") {
        println!("cargo:rustc-link-search=native={}/lib", torch_path);
    } else {
        // Try common installation paths
        let common_paths = vec![
            "/usr/local/lib",
            "/usr/lib",
            "/opt/libtorch/lib",
            "/opt/homebrew/lib",  // macOS Apple Silicon
        ];

        for path in common_paths {
            let lib_path = PathBuf::from(path);
            if lib_path.join("libtorch.so").exists()
                || lib_path.join("libtorch.dylib").exists()
                || lib_path.join("torch.dll").exists()
            {
                println!("cargo:rustc-link-search=native={}", path);
                break;
            }
        }
    }

    // Link against libtorch
    println!("cargo:rustc-link-lib=torch");
    println!("cargo:rustc-link-lib=c10");  // LibTorch CPU backend

    // Optional: CUDA support
    if env::var("SIMPLE_TORCH_CUDA").is_ok() {
        println!("cargo:rustc-link-lib=torch_cuda");
        println!("cargo:rustc-link-lib=c10_cuda");
    }

    // Platform-specific settings
    if cfg!(target_os = "macos") {
        println!("cargo:rustc-link-arg=-Wl,-rpath,@loader_path");
    } else if cfg!(target_os = "linux") {
        println!("cargo:rustc-link-arg=-Wl,-rpath,$ORIGIN");
    }
}
```

### src/lib.rs - Main Entry Point

```rust
// .build/rust/ffi_torch/src/lib.rs

#![allow(non_camel_case_types)]

use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_void, c_int, c_long};
use std::ptr;
use std::slice;

mod tensor;
mod device;

pub use tensor::*;
pub use device::*;

// ============================================================================
// C API Bindings to LibTorch
// ============================================================================

// These are the actual C functions from libtorch
#[link(name = "torch")]
extern "C" {
    // Tensor creation
    fn at_zeros(dims: *const c_long, ndims: c_int, options: c_int) -> *mut c_void;
    fn at_ones(dims: *const c_long, ndims: c_int, options: c_int) -> *mut c_void;
    fn at_randn(dims: *const c_long, ndims: c_int, options: c_int) -> *mut c_void;

    // Tensor operations
    fn at_add(a: *const c_void, b: *const c_void) -> *mut c_void;
    fn at_mul(a: *const c_void, b: *const c_void) -> *mut c_void;
    fn at_matmul(a: *const c_void, b: *const c_void) -> *mut c_void;

    // Tensor properties
    fn at_shape(tensor: *const c_void, dims_out: *mut c_long) -> c_int;
    fn at_numel(tensor: *const c_void) -> c_long;
    fn at_ndim(tensor: *const c_void) -> c_int;

    // Data access
    fn at_data_ptr(tensor: *const c_void) -> *const c_void;

    // Memory management
    fn at_free(tensor: *mut c_void);

    // Activations
    fn at_relu(tensor: *const c_void) -> *mut c_void;
    fn at_sigmoid(tensor: *const c_void) -> *mut c_void;
    fn at_tanh(tensor: *const c_void) -> *mut c_void;

    // Device management
    fn at_to_device(tensor: *const c_void, device: c_int) -> *mut c_void;
    fn at_cuda_is_available() -> c_int;
}

// ============================================================================
// Simple FFI Type Wrappers
// ============================================================================

/// Opaque handle to a PyTorch tensor
/// This is what Simple code will pass around
#[repr(C)]
pub struct SimpleTorchTensor {
    ptr: *mut c_void,
    owns: bool,
}

impl SimpleTorchTensor {
    fn new(ptr: *mut c_void) -> Self {
        SimpleTorchTensor { ptr, owns: true }
    }

    fn from_ptr(ptr: *mut c_void, owns: bool) -> Self {
        SimpleTorchTensor { ptr, owns }
    }
}

impl Drop for SimpleTorchTensor {
    fn drop(&mut self) {
        if self.owns && !self.ptr.is_null() {
            unsafe {
                at_free(self.ptr);
            }
        }
    }
}

// ============================================================================
// FFI Exports for Simple Runtime
// ============================================================================
// All functions are prefixed with simple_torch_ and use C ABI

const DTYPE_FLOAT32: c_int = 6;  // ScalarType::Float
const DEVICE_CPU: c_int = 0;
const DEVICE_CUDA: c_int = 1;

/// Check if PyTorch FFI is available
#[no_mangle]
pub extern "C" fn simple_torch_available() -> bool {
    true  // If this library loaded, PyTorch is available
}

/// Get PyTorch version string
#[no_mangle]
pub extern "C" fn simple_torch_version() -> *const c_char {
    // Return static string
    "PyTorch 2.x (FFI)\0".as_ptr() as *const c_char
}

/// Check if CUDA is available
#[no_mangle]
pub extern "C" fn simple_torch_cuda_available() -> bool {
    unsafe { at_cuda_is_available() != 0 }
}

// --- Tensor Creation ---

/// Create zero tensor
#[no_mangle]
pub extern "C" fn simple_torch_tensor_zeros(
    dims: *const c_long,
    ndims: c_int,
) -> *mut SimpleTorchTensor {
    unsafe {
        let ptr = at_zeros(dims, ndims, DTYPE_FLOAT32);
        Box::into_raw(Box::new(SimpleTorchTensor::new(ptr)))
    }
}

/// Create ones tensor
#[no_mangle]
pub extern "C" fn simple_torch_tensor_ones(
    dims: *const c_long,
    ndims: c_int,
) -> *mut SimpleTorchTensor {
    unsafe {
        let ptr = at_ones(dims, ndims, DTYPE_FLOAT32);
        Box::into_raw(Box::new(SimpleTorchTensor::new(ptr)))
    }
}

/// Create random normal tensor
#[no_mangle]
pub extern "C" fn simple_torch_tensor_randn(
    dims: *const c_long,
    ndims: c_int,
) -> *mut SimpleTorchTensor {
    unsafe {
        let ptr = at_randn(dims, ndims, DTYPE_FLOAT32);
        Box::into_raw(Box::new(SimpleTorchTensor::new(ptr)))
    }
}

/// Free tensor
#[no_mangle]
pub extern "C" fn simple_torch_tensor_free(tensor: *mut SimpleTorchTensor) {
    if !tensor.is_null() {
        unsafe {
            let _ = Box::from_raw(tensor);  // Drop will handle freeing
        }
    }
}

// --- Tensor Operations ---

/// Add tensors
#[no_mangle]
pub extern "C" fn simple_torch_tensor_add(
    a: *const SimpleTorchTensor,
    b: *const SimpleTorchTensor,
) -> *mut SimpleTorchTensor {
    unsafe {
        let a_ref = &*a;
        let b_ref = &*b;
        let result_ptr = at_add(a_ref.ptr, b_ref.ptr);
        Box::into_raw(Box::new(SimpleTorchTensor::new(result_ptr)))
    }
}

/// Multiply tensors (element-wise)
#[no_mangle]
pub extern "C" fn simple_torch_tensor_mul(
    a: *const SimpleTorchTensor,
    b: *const SimpleTorchTensor,
) -> *mut SimpleTorchTensor {
    unsafe {
        let a_ref = &*a;
        let b_ref = &*b;
        let result_ptr = at_mul(a_ref.ptr, b_ref.ptr);
        Box::into_raw(Box::new(SimpleTorchTensor::new(result_ptr)))
    }
}

/// Matrix multiplication
#[no_mangle]
pub extern "C" fn simple_torch_tensor_matmul(
    a: *const SimpleTorchTensor,
    b: *const SimpleTorchTensor,
) -> *mut SimpleTorchTensor {
    unsafe {
        let a_ref = &*a;
        let b_ref = &*b;
        let result_ptr = at_matmul(a_ref.ptr, b_ref.ptr);
        Box::into_raw(Box::new(SimpleTorchTensor::new(result_ptr)))
    }
}

// --- Tensor Properties ---

/// Get tensor shape
#[no_mangle]
pub extern "C" fn simple_torch_tensor_shape(
    tensor: *const SimpleTorchTensor,
    dims_out: *mut c_long,
    max_dims: c_int,
) -> c_int {
    unsafe {
        let t = &*tensor;
        at_shape(t.ptr, dims_out)
    }
}

/// Get number of dimensions
#[no_mangle]
pub extern "C" fn simple_torch_tensor_ndim(tensor: *const SimpleTorchTensor) -> c_int {
    unsafe {
        let t = &*tensor;
        at_ndim(t.ptr)
    }
}

/// Get number of elements
#[no_mangle]
pub extern "C" fn simple_torch_tensor_numel(tensor: *const SimpleTorchTensor) -> c_long {
    unsafe {
        let t = &*tensor;
        at_numel(t.ptr)
    }
}

// --- Activations ---

/// ReLU activation
#[no_mangle]
pub extern "C" fn simple_torch_relu(
    tensor: *const SimpleTorchTensor,
) -> *mut SimpleTorchTensor {
    unsafe {
        let t = &*tensor;
        let result_ptr = at_relu(t.ptr);
        Box::into_raw(Box::new(SimpleTorchTensor::new(result_ptr)))
    }
}

/// Sigmoid activation
#[no_mangle]
pub extern "C" fn simple_torch_sigmoid(
    tensor: *const SimpleTorchTensor,
) -> *mut SimpleTorchTensor {
    unsafe {
        let t = &*tensor;
        let result_ptr = at_sigmoid(t.ptr);
        Box::into_raw(Box::new(SimpleTorchTensor::new(result_ptr)))
    }
}

/// Tanh activation
#[no_mangle]
pub extern "C" fn simple_torch_tanh(
    tensor: *const SimpleTorchTensor,
) -> *mut SimpleTorchTensor {
    unsafe {
        let t = &*tensor;
        let result_ptr = at_tanh(t.ptr);
        Box::into_raw(Box::new(SimpleTorchTensor::new(result_ptr)))
    }
}

// --- Device Management ---

/// Move tensor to device
#[no_mangle]
pub extern "C" fn simple_torch_tensor_to_device(
    tensor: *const SimpleTorchTensor,
    device: c_int,  // 0 = CPU, 1 = CUDA
) -> *mut SimpleTorchTensor {
    unsafe {
        let t = &*tensor;
        let result_ptr = at_to_device(t.ptr, device);
        Box::into_raw(Box::new(SimpleTorchTensor::new(result_ptr)))
    }
}
```

## Tier 2: SFFI Bindings (Simple)

### src/lib/torch/ffi.spl

```simple
# SFFI bindings to PyTorch Rust wrapper
# Maps Rust C exports to Simple extern declarations

# --- Opaque Handle Type ---
extern type TorchTensorHandle

# --- Library Info ---
extern fn rt_torch_available() -> bool
extern fn rt_torch_version() -> text
extern fn rt_torch_cuda_available() -> bool

# --- Tensor Creation ---
extern fn rt_torch_tensor_zeros(dims: [i64], ndims: i64) -> TorchTensorHandle
extern fn rt_torch_tensor_ones(dims: [i64], ndims: i64) -> TorchTensorHandle
extern fn rt_torch_tensor_randn(dims: [i64], ndims: i64) -> TorchTensorHandle
extern fn rt_torch_tensor_free(handle: TorchTensorHandle)

# --- Tensor Operations ---
extern fn rt_torch_tensor_add(a: TorchTensorHandle, b: TorchTensorHandle) -> TorchTensorHandle
extern fn rt_torch_tensor_mul(a: TorchTensorHandle, b: TorchTensorHandle) -> TorchTensorHandle
extern fn rt_torch_tensor_matmul(a: TorchTensorHandle, b: TorchTensorHandle) -> TorchTensorHandle

# --- Tensor Properties ---
extern fn rt_torch_tensor_shape(handle: TorchTensorHandle, dims_out: [i64], max_dims: i64) -> i64
extern fn rt_torch_tensor_ndim(handle: TorchTensorHandle) -> i64
extern fn rt_torch_tensor_numel(handle: TorchTensorHandle) -> i64

# --- Activations ---
extern fn rt_torch_relu(x: TorchTensorHandle) -> TorchTensorHandle
extern fn rt_torch_sigmoid(x: TorchTensorHandle) -> TorchTensorHandle
extern fn rt_torch_tanh(x: TorchTensorHandle) -> TorchTensorHandle

# --- Device Management ---
extern fn rt_torch_tensor_to_device(handle: TorchTensorHandle, device: i64) -> TorchTensorHandle
```

## Tier 3: Simple API Layer

See design doc: `doc/design/sffi_external_library_pattern.md`

## Build & Installation

### Prerequisites

**Ubuntu/Debian:**
```bash
# Install libtorch
wget https://download.pytorch.org/libtorch/cpu/libtorch-cxx11-abi-shared-with-deps-2.1.0%2Bcpu.zip
unzip libtorch-*.zip -d /opt/
export LIBTORCH=/opt/libtorch
export LD_LIBRARY_PATH=$LIBTORCH/lib:$LD_LIBRARY_PATH
```

**macOS:**
```bash
# Via Homebrew (if available) or download manually
wget https://download.pytorch.org/libtorch/cpu/libtorch-macos-2.1.0.zip
unzip libtorch-*.zip -d /opt/
export LIBTORCH=/opt/libtorch
export DYLD_LIBRARY_PATH=$LIBTORCH/lib:$DYLD_LIBRARY_PATH
```

**Windows:**
```powershell
# Download and extract libtorch
# Set environment variable
$env:LIBTORCH = "C:\libtorch"
$env:PATH = "$env:LIBTORCH\lib;$env:PATH"
```

### Building the Wrapper

```bash
# From Simple project root
cd .build/rust/ffi_torch

# Build the wrapper
cargo build --release

# Output: target/release/libsimple_torch_ffi.so (Linux)
#         target/release/libsimple_torch_ffi.dylib (macOS)
#         target/release/simple_torch_ffi.dll (Windows)

# Copy to Simple runtime library path
cp target/release/libsimple_torch_ffi.* ../../../lib/
```

### Integration with Simple Build

```bash
# Simple build system automatically builds FFI wrappers
bin/simple build --with-torch

# Or build all FFI wrappers
bin/simple build --ffi-all
```

## Testing

### Rust Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tensor_creation() {
        let dims = vec![2i64, 3i64];
        let tensor = unsafe {
            simple_torch_tensor_zeros(dims.as_ptr(), 2)
        };
        assert!(!tensor.is_null());

        let ndim = unsafe { simple_torch_tensor_ndim(tensor) };
        assert_eq!(ndim, 2);

        unsafe { simple_torch_tensor_free(tensor); }
    }
}
```

### Simple Integration Tests

```simple
# test/lib/torch_ffi_spec.spl
use lib.torch.ffi.*

describe "PyTorch FFI":
    it "is available":
        expect(rt_torch_available()).to_equal(true)

    it "creates tensors":
        val handle = rt_torch_tensor_zeros([2, 3], 2)
        val ndim = rt_torch_tensor_ndim(handle)
        expect(ndim).to_equal(2)
        rt_torch_tensor_free(handle)
```

## Performance Considerations

1. **Zero-copy where possible**: Use `from_blob` for existing data
2. **Minimize round-trips**: Batch operations in Simple layer
3. **GPU transfers**: Minimize CPU↔GPU copies
4. **Memory pooling**: Reuse tensors to reduce allocations

## Limitations

1. **No C++ exceptions**: Must convert to error codes
2. **Limited types**: Only support f32/f64/i64 initially
3. **No autograd**: Inference only for now
4. **No JIT**: No TorchScript support

## Future Work

1. **Autograd support**: Backward pass, gradients
2. **More dtypes**: int32, bool, complex
3. **TorchScript**: JIT compilation
4. **More NN modules**: Conv2d, LSTM, etc.
5. **Distributed**: Multi-GPU, multi-node

## References

- [PyTorch C++ API Docs](https://pytorch.org/cppdocs/)
- [LibTorch Installation](https://pytorch.org/get-started/locally/)
- [Rust FFI Guide](https://doc.rust-lang.org/nomicon/ffi.html)
