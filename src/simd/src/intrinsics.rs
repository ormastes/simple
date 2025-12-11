//! SIMD Intrinsics
//!
//! This module provides low-level SIMD intrinsics that map more directly
//! to CPU instructions. These are used by the codegen layer.

use crate::types::*;

/// SIMD intrinsic operations for codegen.
///
/// These functions represent primitive SIMD operations that can be
/// lowered to specific CPU instructions by the compiler.
pub trait SimdIntrinsics {
    /// Vector addition.
    fn simd_add(a: Self, b: Self) -> Self;
    /// Vector subtraction.
    fn simd_sub(a: Self, b: Self) -> Self;
    /// Vector multiplication.
    fn simd_mul(a: Self, b: Self) -> Self;
    /// Vector division.
    fn simd_div(a: Self, b: Self) -> Self;
}

/// Implement SimdIntrinsics for types that support standard arithmetic operators.
macro_rules! impl_simd_intrinsics_std {
    ($($ty:ty),+) => {
        $(
            impl SimdIntrinsics for $ty {
                #[inline]
                fn simd_add(a: Self, b: Self) -> Self { a + b }
                #[inline]
                fn simd_sub(a: Self, b: Self) -> Self { a - b }
                #[inline]
                fn simd_mul(a: Self, b: Self) -> Self { a * b }
                #[inline]
                fn simd_div(a: Self, b: Self) -> Self { a / b }
            }
        )+
    };
}

impl_simd_intrinsics_std!(F32x4, F32x8);

/// Implement SimdIntrinsics for types with custom div (integer types without Div trait)
macro_rules! impl_simd_intrinsics_int {
    ($ty:ty, $div_expr:expr) => {
        impl SimdIntrinsics for $ty {
            #[inline]
            fn simd_add(a: Self, b: Self) -> Self { a + b }
            #[inline]
            fn simd_sub(a: Self, b: Self) -> Self { a - b }
            #[inline]
            fn simd_mul(a: Self, b: Self) -> Self { a * b }
            #[inline]
            fn simd_div(a: Self, b: Self) -> Self { $div_expr(a, b) }
        }
    };
}

// I32x4 needs lane-wise division since it doesn't implement Div
impl_simd_intrinsics_int!(I32x4, |a: I32x4, b: I32x4| I32x4([
    a.0[0] / b.0[0],
    a.0[1] / b.0[1],
    a.0[2] / b.0[2],
    a.0[3] / b.0[3],
]));

/// Represents a SIMD instruction for the MIR/codegen layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimdOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,

    // Comparisons
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Bitwise
    And,
    Or,
    Xor,
    Not,

    // Math
    Sqrt,
    Abs,
    Floor,
    Ceil,
    Round,
    Recip,
    Fma,

    // Reductions
    Sum,
    Product,
    Min,
    Max,
    All,
    Any,

    // Shuffles
    Shuffle,
    Blend,
    Swizzle,

    // Memory
    Load,
    Store,
    LoadMasked,
    StoreMasked,
    Gather,
    Scatter,

    // Conversions
    Splat,
    Extract,
    Insert,
    Cast,
}

/// SIMD instruction descriptor for MIR.
#[derive(Debug, Clone)]
pub struct SimdInstruction {
    pub op: SimdOp,
    pub element_type: SimdElementType,
    pub lanes: LaneCount,
}

impl SimdInstruction {
    pub fn new(op: SimdOp, element_type: SimdElementType, lanes: LaneCount) -> Self {
        SimdInstruction {
            op,
            element_type,
            lanes,
        }
    }

    /// Get the result type of this instruction.
    pub fn result_type(&self) -> SimdType {
        match self.op {
            // Comparisons return bool vectors
            SimdOp::Eq | SimdOp::Ne | SimdOp::Lt | SimdOp::Le | SimdOp::Gt | SimdOp::Ge => {
                SimdType {
                    element: SimdElementType::Bool,
                    lanes: self.lanes,
                }
            }
            // Reductions return scalars (represented as single-lane)
            SimdOp::Sum | SimdOp::Product | SimdOp::Min | SimdOp::Max => SimdType {
                element: self.element_type,
                lanes: LaneCount::Two, // Scalar, but we represent as min lanes
            },
            SimdOp::All | SimdOp::Any => SimdType {
                element: SimdElementType::Bool,
                lanes: LaneCount::Two,
            },
            // Extract returns scalar
            SimdOp::Extract => SimdType {
                element: self.element_type,
                lanes: LaneCount::Two,
            },
            // Most ops preserve type
            _ => SimdType {
                element: self.element_type,
                lanes: self.lanes,
            },
        }
    }
}

/// Cranelift SIMD type mapping.
///
/// Maps Simple SIMD types to Cranelift IR types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CraneliftSimdType {
    I8x16,
    I16x8,
    I32x4,
    I64x2,
    F32x4,
    F64x2,
}

impl CraneliftSimdType {
    /// Get the Cranelift type for a Simple SIMD type.
    pub fn from_simd_type(simd_type: &SimdType) -> Option<Self> {
        match (simd_type.element, simd_type.lanes) {
            (SimdElementType::F32, LaneCount::Four) => Some(CraneliftSimdType::F32x4),
            (SimdElementType::F64, LaneCount::Two) => Some(CraneliftSimdType::F64x2),
            (SimdElementType::I32, LaneCount::Four) => Some(CraneliftSimdType::I32x4),
            (SimdElementType::I64, LaneCount::Two) => Some(CraneliftSimdType::I64x2),
            (SimdElementType::I16, LaneCount::Eight) => Some(CraneliftSimdType::I16x8),
            (SimdElementType::I8, LaneCount::Sixteen) => Some(CraneliftSimdType::I8x16),
            // Other combinations need to be emulated or use different strategies
            _ => None,
        }
    }

    /// Get the bit width of this SIMD type.
    pub fn bit_width(&self) -> usize {
        128 // All 128-bit vectors for now
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simd_intrinsics() {
        let a = F32x4::new([1.0, 2.0, 3.0, 4.0]);
        let b = F32x4::new([5.0, 6.0, 7.0, 8.0]);

        let sum = F32x4::simd_add(a, b);
        assert_eq!(sum.0, [6.0, 8.0, 10.0, 12.0]);

        let diff = F32x4::simd_sub(a, b);
        assert_eq!(diff.0, [-4.0, -4.0, -4.0, -4.0]);
    }

    #[test]
    fn test_simd_instruction() {
        let instr = SimdInstruction::new(SimdOp::Add, SimdElementType::F32, LaneCount::Four);

        let result_type = instr.result_type();
        assert_eq!(result_type.element, SimdElementType::F32);
        assert_eq!(result_type.lanes, LaneCount::Four);
    }

    #[test]
    fn test_comparison_result_type() {
        let instr = SimdInstruction::new(SimdOp::Lt, SimdElementType::F32, LaneCount::Four);

        let result_type = instr.result_type();
        assert_eq!(result_type.element, SimdElementType::Bool);
        assert_eq!(result_type.lanes, LaneCount::Four);
    }

    #[test]
    fn test_cranelift_mapping() {
        let simd_type = SimdType::new(SimdElementType::F32, LaneCount::Four).unwrap();
        let cl_type = CraneliftSimdType::from_simd_type(&simd_type);
        assert_eq!(cl_type, Some(CraneliftSimdType::F32x4));
    }
}
