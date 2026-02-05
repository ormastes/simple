//! SIMD Vector Types
//!
//! This module defines the core SIMD vector types for the Simple language.
//! Types are organized by element type and lane count.

use std::fmt;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Index, Mul, Neg, Not, Sub};

// Include core type definitions
include!("types_core.rs");

// Include F32 implementations
include!("types_f32.rs");

// Include integer implementations
include!("types_int.rs");
