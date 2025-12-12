//! GPU Compute Abstractions for Simple Language
//!
//! This crate provides GPU compute abstractions for the Simple programming language.
//! It implements Features #124-129.
//!
//! ## Overview
//!
//! The GPU module provides:
//! - Device discovery and context management
//! - GPU buffer allocation and data transfer
//! - Kernel compilation and execution
//! - Work group and synchronization primitives
//!
//! ## Architecture
//!
//! The GPU module is designed to be backend-agnostic:
//! - WGPU backend (default, cross-platform)
//! - CUDA backend (optional, NVIDIA)
//! - Metal backend (optional, Apple)
//!
//! ## Example
//!
//! ```ignore
//! let ctx = gpu::Context::default()?;
//! let a_buf = ctx.alloc_upload(&host_a)?;
//! let b_buf = ctx.alloc_upload(&host_b)?;
//! let out_buf = ctx.alloc::<f32>(1024)?;
//!
//! ctx.launch(kernel, [1024], [256], &[a_buf, b_buf, out_buf])?;
//! ctx.sync()?;
//!
//! let result = out_buf.download()?;
//! ```

mod device;
mod context;
mod buffer;
mod kernel;
mod intrinsics;
mod error;
mod parallel;
mod optimize;
pub mod backend;

pub use device::*;
pub use context::*;
pub use buffer::*;
pub use kernel::*;
pub use intrinsics::*;
pub use error::*;
pub use parallel::*;
pub use optimize::*;
pub use backend::{Backend, get_backend, get_backend_by_type};
