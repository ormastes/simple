//! SIMD Vector Types
//!
//! This module defines the core SIMD vector types for the Simple language.
//! Types are organized by element type and lane count.

use std::fmt;
use std::ops::{Add, Sub, Mul, Div, Neg, Index, BitAnd, BitOr, BitXor, Not};

/// Element types that can be used in SIMD vectors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SimdElementType {
    F64,
    F32,
    I64,
    I32,
    I16,
    I8,
    U64,
    U32,
    U16,
    U8,
    Bool,
}

impl SimdElementType {
    /// Size in bytes of the element type.
    pub fn size_bytes(&self) -> usize {
        match self {
            SimdElementType::F64 | SimdElementType::I64 | SimdElementType::U64 => 8,
            SimdElementType::F32 | SimdElementType::I32 | SimdElementType::U32 => 4,
            SimdElementType::I16 | SimdElementType::U16 => 2,
            SimdElementType::I8 | SimdElementType::U8 | SimdElementType::Bool => 1,
        }
    }

    /// Whether this is a floating-point type.
    pub fn is_float(&self) -> bool {
        matches!(self, SimdElementType::F32 | SimdElementType::F64)
    }

    /// Whether this is a signed integer type.
    pub fn is_signed(&self) -> bool {
        matches!(
            self,
            SimdElementType::I8 | SimdElementType::I16 | SimdElementType::I32 | SimdElementType::I64
        )
    }
}

/// Supported lane counts for SIMD vectors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LaneCount {
    Two = 2,
    Four = 4,
    Eight = 8,
    Sixteen = 16,
}

impl LaneCount {
    pub fn as_usize(&self) -> usize {
        *self as usize
    }
}

/// SIMD vector type descriptor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SimdType {
    pub element: SimdElementType,
    pub lanes: LaneCount,
}

impl SimdType {
    pub fn new(element: SimdElementType, lanes: LaneCount) -> Option<Self> {
        // Validate that the combination is supported
        let valid = match (element, lanes) {
            // f64: 2, 4, 8 lanes
            (SimdElementType::F64, LaneCount::Two | LaneCount::Four | LaneCount::Eight) => true,
            // f32, i32, u32: 2, 4, 8, 16 lanes
            (
                SimdElementType::F32 | SimdElementType::I32 | SimdElementType::U32,
                _,
            ) => true,
            // i64, u64: 2, 4, 8 lanes
            (
                SimdElementType::I64 | SimdElementType::U64,
                LaneCount::Two | LaneCount::Four | LaneCount::Eight,
            ) => true,
            // i16, u16, i8, u8, bool: all lane counts
            (
                SimdElementType::I16
                | SimdElementType::U16
                | SimdElementType::I8
                | SimdElementType::U8
                | SimdElementType::Bool,
                _,
            ) => true,
            _ => false,
        };

        if valid {
            Some(SimdType { element, lanes })
        } else {
            None
        }
    }

    /// Total size in bytes of the vector.
    pub fn size_bytes(&self) -> usize {
        self.element.size_bytes() * self.lanes.as_usize()
    }
}

impl fmt::Display for SimdType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let elem = match self.element {
            SimdElementType::F64 => "f64",
            SimdElementType::F32 => "f32",
            SimdElementType::I64 => "i64",
            SimdElementType::I32 => "i32",
            SimdElementType::I16 => "i16",
            SimdElementType::I8 => "i8",
            SimdElementType::U64 => "u64",
            SimdElementType::U32 => "u32",
            SimdElementType::U16 => "u16",
            SimdElementType::U8 => "u8",
            SimdElementType::Bool => "bool",
        };
        write!(f, "vec[{}, {}]", self.lanes.as_usize(), elem)
    }
}

// =============================================================================
// Concrete Vector Types
// =============================================================================

/// 4-lane f32 vector (128-bit).
#[derive(Clone, Copy, PartialEq)]
#[repr(align(16))]
pub struct F32x4(pub [f32; 4]);

/// 8-lane f32 vector (256-bit).
#[derive(Clone, Copy, PartialEq)]
#[repr(align(32))]
pub struct F32x8(pub [f32; 8]);

/// 2-lane f64 vector (128-bit).
#[derive(Clone, Copy, PartialEq)]
#[repr(align(16))]
pub struct F64x2(pub [f64; 2]);

/// 4-lane f64 vector (256-bit).
#[derive(Clone, Copy, PartialEq)]
#[repr(align(32))]
pub struct F64x4(pub [f64; 4]);

/// 4-lane i32 vector (128-bit).
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(align(16))]
pub struct I32x4(pub [i32; 4]);

/// 8-lane i32 vector (256-bit).
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(align(32))]
pub struct I32x8(pub [i32; 8]);

/// 2-lane i64 vector (128-bit).
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(align(16))]
pub struct I64x2(pub [i64; 2]);

/// 4-lane i64 vector (256-bit).
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(align(32))]
pub struct I64x4(pub [i64; 4]);

/// 4-lane bool vector for masking.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(align(16))]
pub struct Mask32x4(pub [i32; 4]);

/// 8-lane bool vector for masking.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(align(32))]
pub struct Mask32x8(pub [i32; 8]);

// =============================================================================
// F32x4 Implementation
// =============================================================================

impl F32x4 {
    pub const LANES: usize = 4;

    /// Create a new vector from an array.
    #[inline]
    pub fn new(values: [f32; 4]) -> Self {
        F32x4(values)
    }

    /// Create a vector with all lanes set to the same value.
    #[inline]
    pub fn splat(value: f32) -> Self {
        F32x4([value; 4])
    }

    /// Create a zero vector.
    #[inline]
    pub fn zero() -> Self {
        F32x4([0.0; 4])
    }

    /// Extract a single lane.
    #[inline]
    pub fn extract(&self, index: usize) -> f32 {
        self.0[index]
    }

    /// Create a new vector with one lane replaced.
    #[inline]
    pub fn with(&self, index: usize, value: f32) -> Self {
        let mut result = *self;
        result.0[index] = value;
        result
    }

    /// Load from a slice (must have at least 4 elements from offset).
    #[inline]
    pub fn load(slice: &[f32], offset: usize) -> Self {
        F32x4([
            slice[offset],
            slice[offset + 1],
            slice[offset + 2],
            slice[offset + 3],
        ])
    }

    /// Store to a slice.
    #[inline]
    pub fn store(&self, slice: &mut [f32], offset: usize) {
        slice[offset] = self.0[0];
        slice[offset + 1] = self.0[1];
        slice[offset + 2] = self.0[2];
        slice[offset + 3] = self.0[3];
    }

    /// Horizontal sum of all lanes.
    #[inline]
    pub fn sum(&self) -> f32 {
        self.0[0] + self.0[1] + self.0[2] + self.0[3]
    }

    /// Horizontal product of all lanes.
    #[inline]
    pub fn product(&self) -> f32 {
        self.0[0] * self.0[1] * self.0[2] * self.0[3]
    }

    /// Minimum value across all lanes.
    #[inline]
    pub fn min_element(&self) -> f32 {
        self.0.iter().cloned().fold(f32::INFINITY, f32::min)
    }

    /// Maximum value across all lanes.
    #[inline]
    pub fn max_element(&self) -> f32 {
        self.0.iter().cloned().fold(f32::NEG_INFINITY, f32::max)
    }

    /// Lane-wise minimum.
    #[inline]
    pub fn min(&self, other: Self) -> Self {
        F32x4([
            self.0[0].min(other.0[0]),
            self.0[1].min(other.0[1]),
            self.0[2].min(other.0[2]),
            self.0[3].min(other.0[3]),
        ])
    }

    /// Lane-wise maximum.
    #[inline]
    pub fn max(&self, other: Self) -> Self {
        F32x4([
            self.0[0].max(other.0[0]),
            self.0[1].max(other.0[1]),
            self.0[2].max(other.0[2]),
            self.0[3].max(other.0[3]),
        ])
    }

    /// Lane-wise absolute value.
    #[inline]
    pub fn abs(&self) -> Self {
        F32x4([
            self.0[0].abs(),
            self.0[1].abs(),
            self.0[2].abs(),
            self.0[3].abs(),
        ])
    }

    /// Lane-wise square root.
    #[inline]
    pub fn sqrt(&self) -> Self {
        F32x4([
            self.0[0].sqrt(),
            self.0[1].sqrt(),
            self.0[2].sqrt(),
            self.0[3].sqrt(),
        ])
    }

    /// Lane-wise reciprocal (1/x).
    #[inline]
    pub fn recip(&self) -> Self {
        F32x4([
            1.0 / self.0[0],
            1.0 / self.0[1],
            1.0 / self.0[2],
            1.0 / self.0[3],
        ])
    }

    /// Lane-wise floor.
    #[inline]
    pub fn floor(&self) -> Self {
        F32x4([
            self.0[0].floor(),
            self.0[1].floor(),
            self.0[2].floor(),
            self.0[3].floor(),
        ])
    }

    /// Lane-wise ceil.
    #[inline]
    pub fn ceil(&self) -> Self {
        F32x4([
            self.0[0].ceil(),
            self.0[1].ceil(),
            self.0[2].ceil(),
            self.0[3].ceil(),
        ])
    }

    /// Lane-wise round.
    #[inline]
    pub fn round(&self) -> Self {
        F32x4([
            self.0[0].round(),
            self.0[1].round(),
            self.0[2].round(),
            self.0[3].round(),
        ])
    }

    /// Fused multiply-add: self * a + b.
    #[inline]
    pub fn fma(&self, a: Self, b: Self) -> Self {
        F32x4([
            self.0[0].mul_add(a.0[0], b.0[0]),
            self.0[1].mul_add(a.0[1], b.0[1]),
            self.0[2].mul_add(a.0[2], b.0[2]),
            self.0[3].mul_add(a.0[3], b.0[3]),
        ])
    }

    /// Compare less-than, returning a mask.
    #[inline]
    pub fn lt(&self, other: Self) -> Mask32x4 {
        Mask32x4([
            if self.0[0] < other.0[0] { -1 } else { 0 },
            if self.0[1] < other.0[1] { -1 } else { 0 },
            if self.0[2] < other.0[2] { -1 } else { 0 },
            if self.0[3] < other.0[3] { -1 } else { 0 },
        ])
    }

    /// Compare less-than-or-equal, returning a mask.
    #[inline]
    pub fn le(&self, other: Self) -> Mask32x4 {
        Mask32x4([
            if self.0[0] <= other.0[0] { -1 } else { 0 },
            if self.0[1] <= other.0[1] { -1 } else { 0 },
            if self.0[2] <= other.0[2] { -1 } else { 0 },
            if self.0[3] <= other.0[3] { -1 } else { 0 },
        ])
    }

    /// Compare greater-than, returning a mask.
    #[inline]
    pub fn gt(&self, other: Self) -> Mask32x4 {
        Mask32x4([
            if self.0[0] > other.0[0] { -1 } else { 0 },
            if self.0[1] > other.0[1] { -1 } else { 0 },
            if self.0[2] > other.0[2] { -1 } else { 0 },
            if self.0[3] > other.0[3] { -1 } else { 0 },
        ])
    }

    /// Compare equal, returning a mask.
    #[inline]
    pub fn eq(&self, other: Self) -> Mask32x4 {
        Mask32x4([
            if self.0[0] == other.0[0] { -1 } else { 0 },
            if self.0[1] == other.0[1] { -1 } else { 0 },
            if self.0[2] == other.0[2] { -1 } else { 0 },
            if self.0[3] == other.0[3] { -1 } else { 0 },
        ])
    }

    /// Select lanes based on mask: mask ? self : other.
    #[inline]
    pub fn select(mask: Mask32x4, if_true: Self, if_false: Self) -> Self {
        F32x4([
            if mask.0[0] != 0 { if_true.0[0] } else { if_false.0[0] },
            if mask.0[1] != 0 { if_true.0[1] } else { if_false.0[1] },
            if mask.0[2] != 0 { if_true.0[2] } else { if_false.0[2] },
            if mask.0[3] != 0 { if_true.0[3] } else { if_false.0[3] },
        ])
    }

    /// Shuffle lanes based on indices.
    #[inline]
    pub fn shuffle(&self, indices: [usize; 4]) -> Self {
        F32x4([
            self.0[indices[0]],
            self.0[indices[1]],
            self.0[indices[2]],
            self.0[indices[3]],
        ])
    }

    /// Swizzle: get lanes by name (0=x, 1=y, 2=z, 3=w).
    #[inline]
    pub fn x(&self) -> f32 { self.0[0] }
    #[inline]
    pub fn y(&self) -> f32 { self.0[1] }
    #[inline]
    pub fn z(&self) -> f32 { self.0[2] }
    #[inline]
    pub fn w(&self) -> f32 { self.0[3] }

    /// Gather from slice using indices.
    #[inline]
    pub fn gather(slice: &[f32], indices: I32x4) -> Self {
        F32x4([
            slice[indices.0[0] as usize],
            slice[indices.0[1] as usize],
            slice[indices.0[2] as usize],
            slice[indices.0[3] as usize],
        ])
    }

    /// Scatter to slice using indices.
    #[inline]
    pub fn scatter(&self, slice: &mut [f32], indices: I32x4) {
        slice[indices.0[0] as usize] = self.0[0];
        slice[indices.0[1] as usize] = self.0[1];
        slice[indices.0[2] as usize] = self.0[2];
        slice[indices.0[3] as usize] = self.0[3];
    }
}

impl fmt::Debug for F32x4 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "F32x4({:?})", self.0)
    }
}

impl Default for F32x4 {
    fn default() -> Self {
        Self::zero()
    }
}

impl Index<usize> for F32x4 {
    type Output = f32;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl Add for F32x4 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        F32x4([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
        ])
    }
}

impl Sub for F32x4 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        F32x4([
            self.0[0] - rhs.0[0],
            self.0[1] - rhs.0[1],
            self.0[2] - rhs.0[2],
            self.0[3] - rhs.0[3],
        ])
    }
}

impl Mul for F32x4 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        F32x4([
            self.0[0] * rhs.0[0],
            self.0[1] * rhs.0[1],
            self.0[2] * rhs.0[2],
            self.0[3] * rhs.0[3],
        ])
    }
}

impl Div for F32x4 {
    type Output = Self;

    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        F32x4([
            self.0[0] / rhs.0[0],
            self.0[1] / rhs.0[1],
            self.0[2] / rhs.0[2],
            self.0[3] / rhs.0[3],
        ])
    }
}

impl Neg for F32x4 {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        F32x4([-self.0[0], -self.0[1], -self.0[2], -self.0[3]])
    }
}

// Scalar operations
impl Add<f32> for F32x4 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: f32) -> Self::Output {
        self + F32x4::splat(rhs)
    }
}

impl Mul<f32> for F32x4 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: f32) -> Self::Output {
        self * F32x4::splat(rhs)
    }
}

// =============================================================================
// I32x4 Implementation
// =============================================================================

impl I32x4 {
    pub const LANES: usize = 4;

    #[inline]
    pub fn new(values: [i32; 4]) -> Self {
        I32x4(values)
    }

    #[inline]
    pub fn splat(value: i32) -> Self {
        I32x4([value; 4])
    }

    #[inline]
    pub fn zero() -> Self {
        I32x4([0; 4])
    }

    #[inline]
    pub fn extract(&self, index: usize) -> i32 {
        self.0[index]
    }

    #[inline]
    pub fn with(&self, index: usize, value: i32) -> Self {
        let mut result = *self;
        result.0[index] = value;
        result
    }

    #[inline]
    pub fn load(slice: &[i32], offset: usize) -> Self {
        I32x4([
            slice[offset],
            slice[offset + 1],
            slice[offset + 2],
            slice[offset + 3],
        ])
    }

    #[inline]
    pub fn store(&self, slice: &mut [i32], offset: usize) {
        slice[offset] = self.0[0];
        slice[offset + 1] = self.0[1];
        slice[offset + 2] = self.0[2];
        slice[offset + 3] = self.0[3];
    }

    #[inline]
    pub fn sum(&self) -> i32 {
        self.0[0] + self.0[1] + self.0[2] + self.0[3]
    }

    #[inline]
    pub fn min_element(&self) -> i32 {
        *self.0.iter().min().unwrap()
    }

    #[inline]
    pub fn max_element(&self) -> i32 {
        *self.0.iter().max().unwrap()
    }

    #[inline]
    pub fn min(&self, other: Self) -> Self {
        I32x4([
            self.0[0].min(other.0[0]),
            self.0[1].min(other.0[1]),
            self.0[2].min(other.0[2]),
            self.0[3].min(other.0[3]),
        ])
    }

    #[inline]
    pub fn max(&self, other: Self) -> Self {
        I32x4([
            self.0[0].max(other.0[0]),
            self.0[1].max(other.0[1]),
            self.0[2].max(other.0[2]),
            self.0[3].max(other.0[3]),
        ])
    }

    #[inline]
    pub fn abs(&self) -> Self {
        I32x4([
            self.0[0].abs(),
            self.0[1].abs(),
            self.0[2].abs(),
            self.0[3].abs(),
        ])
    }

    #[inline]
    pub fn lt(&self, other: Self) -> Mask32x4 {
        Mask32x4([
            if self.0[0] < other.0[0] { -1 } else { 0 },
            if self.0[1] < other.0[1] { -1 } else { 0 },
            if self.0[2] < other.0[2] { -1 } else { 0 },
            if self.0[3] < other.0[3] { -1 } else { 0 },
        ])
    }

    #[inline]
    pub fn eq(&self, other: Self) -> Mask32x4 {
        Mask32x4([
            if self.0[0] == other.0[0] { -1 } else { 0 },
            if self.0[1] == other.0[1] { -1 } else { 0 },
            if self.0[2] == other.0[2] { -1 } else { 0 },
            if self.0[3] == other.0[3] { -1 } else { 0 },
        ])
    }

    #[inline]
    pub fn select(mask: Mask32x4, if_true: Self, if_false: Self) -> Self {
        I32x4([
            if mask.0[0] != 0 { if_true.0[0] } else { if_false.0[0] },
            if mask.0[1] != 0 { if_true.0[1] } else { if_false.0[1] },
            if mask.0[2] != 0 { if_true.0[2] } else { if_false.0[2] },
            if mask.0[3] != 0 { if_true.0[3] } else { if_false.0[3] },
        ])
    }
}

impl fmt::Debug for I32x4 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "I32x4({:?})", self.0)
    }
}

impl Default for I32x4 {
    fn default() -> Self {
        Self::zero()
    }
}

impl Index<usize> for I32x4 {
    type Output = i32;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl Add for I32x4 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        I32x4([
            self.0[0] + rhs.0[0],
            self.0[1] + rhs.0[1],
            self.0[2] + rhs.0[2],
            self.0[3] + rhs.0[3],
        ])
    }
}

impl Sub for I32x4 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        I32x4([
            self.0[0] - rhs.0[0],
            self.0[1] - rhs.0[1],
            self.0[2] - rhs.0[2],
            self.0[3] - rhs.0[3],
        ])
    }
}

impl Mul for I32x4 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        I32x4([
            self.0[0] * rhs.0[0],
            self.0[1] * rhs.0[1],
            self.0[2] * rhs.0[2],
            self.0[3] * rhs.0[3],
        ])
    }
}

impl BitAnd for I32x4 {
    type Output = Self;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        I32x4([
            self.0[0] & rhs.0[0],
            self.0[1] & rhs.0[1],
            self.0[2] & rhs.0[2],
            self.0[3] & rhs.0[3],
        ])
    }
}

impl BitOr for I32x4 {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        I32x4([
            self.0[0] | rhs.0[0],
            self.0[1] | rhs.0[1],
            self.0[2] | rhs.0[2],
            self.0[3] | rhs.0[3],
        ])
    }
}

impl BitXor for I32x4 {
    type Output = Self;

    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        I32x4([
            self.0[0] ^ rhs.0[0],
            self.0[1] ^ rhs.0[1],
            self.0[2] ^ rhs.0[2],
            self.0[3] ^ rhs.0[3],
        ])
    }
}

impl Neg for I32x4 {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        I32x4([-self.0[0], -self.0[1], -self.0[2], -self.0[3]])
    }
}

// =============================================================================
// Mask32x4 Implementation
// =============================================================================

impl Mask32x4 {
    pub const LANES: usize = 4;

    #[inline]
    pub fn new(values: [bool; 4]) -> Self {
        Mask32x4([
            if values[0] { -1 } else { 0 },
            if values[1] { -1 } else { 0 },
            if values[2] { -1 } else { 0 },
            if values[3] { -1 } else { 0 },
        ])
    }

    #[inline]
    pub fn all_true() -> Self {
        Mask32x4([-1; 4])
    }

    #[inline]
    pub fn all_false() -> Self {
        Mask32x4([0; 4])
    }

    /// Test if all lanes are true.
    #[inline]
    pub fn all(&self) -> bool {
        self.0[0] != 0 && self.0[1] != 0 && self.0[2] != 0 && self.0[3] != 0
    }

    /// Test if any lane is true.
    #[inline]
    pub fn any(&self) -> bool {
        self.0[0] != 0 || self.0[1] != 0 || self.0[2] != 0 || self.0[3] != 0
    }

    /// Test if no lanes are true.
    #[inline]
    pub fn none(&self) -> bool {
        !self.any()
    }

    /// Get a single lane as bool.
    #[inline]
    pub fn test(&self, index: usize) -> bool {
        self.0[index] != 0
    }
}

impl fmt::Debug for Mask32x4 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Mask32x4([{}, {}, {}, {}])",
            self.test(0),
            self.test(1),
            self.test(2),
            self.test(3)
        )
    }
}

impl BitAnd for Mask32x4 {
    type Output = Self;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        Mask32x4([
            self.0[0] & rhs.0[0],
            self.0[1] & rhs.0[1],
            self.0[2] & rhs.0[2],
            self.0[3] & rhs.0[3],
        ])
    }
}

impl BitOr for Mask32x4 {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        Mask32x4([
            self.0[0] | rhs.0[0],
            self.0[1] | rhs.0[1],
            self.0[2] | rhs.0[2],
            self.0[3] | rhs.0[3],
        ])
    }
}

impl Not for Mask32x4 {
    type Output = Self;

    #[inline]
    fn not(self) -> Self::Output {
        Mask32x4([!self.0[0], !self.0[1], !self.0[2], !self.0[3]])
    }
}

// =============================================================================
// F32x8 Implementation (256-bit)
// =============================================================================

impl F32x8 {
    pub const LANES: usize = 8;

    #[inline]
    pub fn new(values: [f32; 8]) -> Self {
        F32x8(values)
    }

    #[inline]
    pub fn splat(value: f32) -> Self {
        F32x8([value; 8])
    }

    #[inline]
    pub fn zero() -> Self {
        F32x8([0.0; 8])
    }

    #[inline]
    pub fn extract(&self, index: usize) -> f32 {
        self.0[index]
    }

    #[inline]
    pub fn load(slice: &[f32], offset: usize) -> Self {
        let mut result = [0.0f32; 8];
        result.copy_from_slice(&slice[offset..offset + 8]);
        F32x8(result)
    }

    #[inline]
    pub fn store(&self, slice: &mut [f32], offset: usize) {
        slice[offset..offset + 8].copy_from_slice(&self.0);
    }

    #[inline]
    pub fn sum(&self) -> f32 {
        self.0.iter().sum()
    }
}

impl fmt::Debug for F32x8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "F32x8({:?})", self.0)
    }
}

impl Add for F32x8 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        let mut result = [0.0f32; 8];
        for i in 0..8 {
            result[i] = self.0[i] + rhs.0[i];
        }
        F32x8(result)
    }
}

impl Sub for F32x8 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        let mut result = [0.0f32; 8];
        for i in 0..8 {
            result[i] = self.0[i] - rhs.0[i];
        }
        F32x8(result)
    }
}

impl Mul for F32x8 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        let mut result = [0.0f32; 8];
        for i in 0..8 {
            result[i] = self.0[i] * rhs.0[i];
        }
        F32x8(result)
    }
}

impl Div for F32x8 {
    type Output = Self;

    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        let mut result = [0.0f32; 8];
        for i in 0..8 {
            result[i] = self.0[i] / rhs.0[i];
        }
        F32x8(result)
    }
}

// =============================================================================
// F64x2 Implementation (128-bit)
// =============================================================================

impl F64x2 {
    pub const LANES: usize = 2;

    #[inline]
    pub fn new(values: [f64; 2]) -> Self {
        F64x2(values)
    }

    #[inline]
    pub fn splat(value: f64) -> Self {
        F64x2([value; 2])
    }

    #[inline]
    pub fn zero() -> Self {
        F64x2([0.0; 2])
    }

    #[inline]
    pub fn extract(&self, index: usize) -> f64 {
        self.0[index]
    }

    #[inline]
    pub fn load(slice: &[f64], offset: usize) -> Self {
        F64x2([slice[offset], slice[offset + 1]])
    }

    #[inline]
    pub fn store(&self, slice: &mut [f64], offset: usize) {
        slice[offset] = self.0[0];
        slice[offset + 1] = self.0[1];
    }

    #[inline]
    pub fn sum(&self) -> f64 {
        self.0[0] + self.0[1]
    }

    #[inline]
    pub fn sqrt(&self) -> Self {
        F64x2([self.0[0].sqrt(), self.0[1].sqrt()])
    }

    #[inline]
    pub fn abs(&self) -> Self {
        F64x2([self.0[0].abs(), self.0[1].abs()])
    }
}

impl fmt::Debug for F64x2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "F64x2({:?})", self.0)
    }
}

impl Add for F64x2 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        F64x2([self.0[0] + rhs.0[0], self.0[1] + rhs.0[1]])
    }
}

impl Sub for F64x2 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        F64x2([self.0[0] - rhs.0[0], self.0[1] - rhs.0[1]])
    }
}

impl Mul for F64x2 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        F64x2([self.0[0] * rhs.0[0], self.0[1] * rhs.0[1]])
    }
}

impl Div for F64x2 {
    type Output = Self;

    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        F64x2([self.0[0] / rhs.0[0], self.0[1] / rhs.0[1]])
    }
}

// =============================================================================
// I64x2 Implementation (128-bit)
// =============================================================================

impl I64x2 {
    pub const LANES: usize = 2;

    #[inline]
    pub fn new(values: [i64; 2]) -> Self {
        I64x2(values)
    }

    #[inline]
    pub fn splat(value: i64) -> Self {
        I64x2([value; 2])
    }

    #[inline]
    pub fn zero() -> Self {
        I64x2([0; 2])
    }

    #[inline]
    pub fn extract(&self, index: usize) -> i64 {
        self.0[index]
    }

    #[inline]
    pub fn load(slice: &[i64], offset: usize) -> Self {
        I64x2([slice[offset], slice[offset + 1]])
    }

    #[inline]
    pub fn store(&self, slice: &mut [i64], offset: usize) {
        slice[offset] = self.0[0];
        slice[offset + 1] = self.0[1];
    }

    #[inline]
    pub fn sum(&self) -> i64 {
        self.0[0] + self.0[1]
    }
}

impl fmt::Debug for I64x2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "I64x2({:?})", self.0)
    }
}

impl Add for I64x2 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        I64x2([self.0[0] + rhs.0[0], self.0[1] + rhs.0[1]])
    }
}

impl Sub for I64x2 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        I64x2([self.0[0] - rhs.0[0], self.0[1] - rhs.0[1]])
    }
}

impl Mul for I64x2 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        I64x2([self.0[0] * rhs.0[0], self.0[1] * rhs.0[1]])
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn f32x4_arithmetic() {
        let a = F32x4::new([1.0, 2.0, 3.0, 4.0]);
        let b = F32x4::new([5.0, 6.0, 7.0, 8.0]);

        let sum = a + b;
        assert_eq!(sum.0, [6.0, 8.0, 10.0, 12.0]);

        let diff = a - b;
        assert_eq!(diff.0, [-4.0, -4.0, -4.0, -4.0]);

        let prod = a * b;
        assert_eq!(prod.0, [5.0, 12.0, 21.0, 32.0]);

        let quot = a / b;
        assert!((quot.0[0] - 0.2).abs() < 0.001);
    }

    #[test]
    fn f32x4_reductions() {
        let a = F32x4::new([1.0, 2.0, 3.0, 4.0]);

        assert_eq!(a.sum(), 10.0);
        assert_eq!(a.product(), 24.0);
        assert_eq!(a.min_element(), 1.0);
        assert_eq!(a.max_element(), 4.0);
    }

    #[test]
    fn f32x4_math() {
        let a = F32x4::new([1.0, 4.0, 9.0, 16.0]);
        let sqrts = a.sqrt();
        assert_eq!(sqrts.0, [1.0, 2.0, 3.0, 4.0]);

        let neg = F32x4::new([-1.0, 2.0, -3.0, 4.0]);
        let abs_v = neg.abs();
        assert_eq!(abs_v.0, [1.0, 2.0, 3.0, 4.0]);
    }

    #[test]
    fn f32x4_comparison() {
        let a = F32x4::new([1.0, 2.0, 3.0, 4.0]);
        let b = F32x4::new([2.0, 2.0, 2.0, 2.0]);

        let lt = a.lt(b);
        assert!(lt.test(0));
        assert!(!lt.test(1));
        assert!(!lt.test(2));
        assert!(!lt.test(3));
    }

    #[test]
    fn f32x4_select() {
        let mask = Mask32x4::new([true, false, true, false]);
        let a = F32x4::new([1.0, 2.0, 3.0, 4.0]);
        let b = F32x4::new([5.0, 6.0, 7.0, 8.0]);

        let selected = F32x4::select(mask, a, b);
        assert_eq!(selected.0, [1.0, 6.0, 3.0, 8.0]);
    }

    #[test]
    fn f32x4_shuffle() {
        let a = F32x4::new([1.0, 2.0, 3.0, 4.0]);
        let shuffled = a.shuffle([3, 2, 1, 0]);
        assert_eq!(shuffled.0, [4.0, 3.0, 2.0, 1.0]);
    }

    #[test]
    fn f32x4_load_store() {
        let data = [1.0f32, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
        let v = F32x4::load(&data, 2);
        assert_eq!(v.0, [3.0, 4.0, 5.0, 6.0]);

        let mut out = [0.0f32; 8];
        v.store(&mut out, 4);
        assert_eq!(out, [0.0, 0.0, 0.0, 0.0, 3.0, 4.0, 5.0, 6.0]);
    }

    #[test]
    fn f32x4_gather_scatter() {
        let data = [10.0f32, 20.0, 30.0, 40.0, 50.0, 60.0, 70.0, 80.0];
        let indices = I32x4::new([0, 2, 4, 6]);

        let gathered = F32x4::gather(&data, indices);
        assert_eq!(gathered.0, [10.0, 30.0, 50.0, 70.0]);

        let mut out = [0.0f32; 8];
        gathered.scatter(&mut out, indices);
        assert_eq!(out, [10.0, 0.0, 30.0, 0.0, 50.0, 0.0, 70.0, 0.0]);
    }

    #[test]
    fn i32x4_arithmetic() {
        let a = I32x4::new([1, 2, 3, 4]);
        let b = I32x4::new([5, 6, 7, 8]);

        let sum = a + b;
        assert_eq!(sum.0, [6, 8, 10, 12]);

        let diff = a - b;
        assert_eq!(diff.0, [-4, -4, -4, -4]);

        let prod = a * b;
        assert_eq!(prod.0, [5, 12, 21, 32]);
    }

    #[test]
    fn i32x4_bitwise() {
        let a = I32x4::new([0b1100, 0b1010, 0b1111, 0b0000]);
        let b = I32x4::new([0b1010, 0b1010, 0b0000, 0b1111]);

        let and = a & b;
        assert_eq!(and.0, [0b1000, 0b1010, 0b0000, 0b0000]);

        let or = a | b;
        assert_eq!(or.0, [0b1110, 0b1010, 0b1111, 0b1111]);

        let xor = a ^ b;
        assert_eq!(xor.0, [0b0110, 0b0000, 0b1111, 0b1111]);
    }

    #[test]
    fn mask_operations() {
        let mask = Mask32x4::new([true, false, true, true]);

        assert!(mask.any());
        assert!(!mask.all());
        assert!(!mask.none());

        let inv = !mask;
        assert!(!inv.test(0));
        assert!(inv.test(1));
        assert!(!inv.test(2));
        assert!(!inv.test(3));
    }

    #[test]
    fn f32x8_basic() {
        let a = F32x8::new([1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]);
        let b = F32x8::splat(2.0);

        let sum = a + b;
        assert_eq!(sum.0, [3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]);

        assert_eq!(a.sum(), 36.0);
    }

    #[test]
    fn f64x2_basic() {
        let a = F64x2::new([1.0, 2.0]);
        let b = F64x2::new([3.0, 4.0]);

        let sum = a + b;
        assert_eq!(sum.0, [4.0, 6.0]);

        assert_eq!(a.sum(), 3.0);
    }

    #[test]
    fn simd_type_validation() {
        // Valid combinations
        assert!(SimdType::new(SimdElementType::F32, LaneCount::Four).is_some());
        assert!(SimdType::new(SimdElementType::F64, LaneCount::Four).is_some());
        assert!(SimdType::new(SimdElementType::I32, LaneCount::Sixteen).is_some());

        // f64x16 is not supported
        assert!(SimdType::new(SimdElementType::F64, LaneCount::Sixteen).is_none());
    }

    #[test]
    fn simd_type_display() {
        let t = SimdType::new(SimdElementType::F32, LaneCount::Four).unwrap();
        assert_eq!(format!("{}", t), "vec[4, f32]");
    }
}
