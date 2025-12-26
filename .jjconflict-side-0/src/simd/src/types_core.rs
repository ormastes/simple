// SIMD core types and definitions
// This file is included by types.rs

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

