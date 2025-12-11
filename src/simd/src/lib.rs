//! SIMD Vector Types and Operations for Simple Language
//!
//! This crate provides SIMD (Single Instruction Multiple Data) vector types
//! and operations for the Simple programming language. It implements Features #118-123.
//!
//! ## Overview
//!
//! SIMD vectors are fixed-size, homogeneous arrays optimized for parallel arithmetic.
//! The type `Vec<N, T>` represents a vector of N elements of type T.
//!
//! ## Supported Types
//!
//! - `Vec<2|4|8, f64>` - 64-bit floating point
//! - `Vec<2|4|8|16, f32>` - 32-bit floating point
//! - `Vec<2|4|8, i64>` - 64-bit signed integer
//! - `Vec<2|4|8|16, i32>` - 32-bit signed integer
//! - `Vec<2|4|8|16, i16>` - 16-bit signed integer
//! - `Vec<2|4|8|16, i8>` - 8-bit signed integer
//!
//! ## Example
//!
//! ```ignore
//! let a = F32x4::new([1.0, 2.0, 3.0, 4.0]);
//! let b = F32x4::new([5.0, 6.0, 7.0, 8.0]);
//! let c = a + b;  // [6.0, 8.0, 10.0, 12.0]
//! ```

mod types;
mod ops;
mod intrinsics;
mod detection;

pub use types::*;
pub use ops::*;
pub use intrinsics::*;
pub use detection::*;
