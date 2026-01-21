//! Type mapping from Simple to SPIR-V
//!
//! Maps Simple language types to their SPIR-V equivalents.
//!
//! ## Supported Type Mappings
//!
//! | Simple Type | SPIR-V Type | Bits | Signed |
//! |-------------|-------------|------|--------|
//! | `void`      | OpTypeVoid  | 0    | N/A    |
//! | `bool`      | OpTypeBool  | 1    | N/A    |
//! | `i8`        | OpTypeInt   | 8    | Yes    |
//! | `i16`       | OpTypeInt   | 16   | Yes    |
//! | `i32`       | OpTypeInt   | 32   | Yes    |
//! | `i64`       | OpTypeInt   | 64   | Yes    |
//! | `u8`        | OpTypeInt   | 8    | No     |
//! | `u16`       | OpTypeInt   | 16   | No     |
//! | `u32`       | OpTypeInt   | 32   | No     |
//! | `u64`       | OpTypeInt   | 64   | No     |
//! | `f32`       | OpTypeFloat | 32   | N/A    |
//! | `f64`       | OpTypeFloat | 64   | N/A    |

use crate::error::CompileError;
use crate::hir::TypeId;

/// SPIR-V type category
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpirvTypeCategory {
    /// Void type (no value)
    Void,
    /// Boolean type (true/false)
    Bool,
    /// Integer type (signed or unsigned)
    Int,
    /// Floating-point type
    Float,
    /// Vector type (vec2, vec3, vec4)
    Vector,
    /// Matrix type (mat2x2, mat3x3, mat4x4)
    Matrix,
    /// Array type
    Array,
    /// Struct type
    Struct,
    /// Pointer type
    Pointer,
    /// Unsupported/unknown type
    Unsupported,
}

/// SPIR-V type information
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpirvTypeInfo {
    /// Type category
    pub category: SpirvTypeCategory,
    /// Bit width (for scalars)
    pub bits: u8,
    /// Is signed (for integers)
    pub signed: bool,
    /// Element count (for vectors/arrays)
    pub elements: u32,
    /// Element type ID (for composite types)
    pub element_type: Option<TypeId>,
}

impl SpirvTypeInfo {
    /// Create void type info
    pub const fn void() -> Self {
        Self {
            category: SpirvTypeCategory::Void,
            bits: 0,
            signed: false,
            elements: 0,
            element_type: None,
        }
    }

    /// Create boolean type info
    pub const fn bool() -> Self {
        Self {
            category: SpirvTypeCategory::Bool,
            bits: 1,
            signed: false,
            elements: 0,
            element_type: None,
        }
    }

    /// Create signed integer type info
    pub const fn signed_int(bits: u8) -> Self {
        Self {
            category: SpirvTypeCategory::Int,
            bits,
            signed: true,
            elements: 0,
            element_type: None,
        }
    }

    /// Create unsigned integer type info
    pub const fn unsigned_int(bits: u8) -> Self {
        Self {
            category: SpirvTypeCategory::Int,
            bits,
            signed: false,
            elements: 0,
            element_type: None,
        }
    }

    /// Create float type info
    pub const fn float(bits: u8) -> Self {
        Self {
            category: SpirvTypeCategory::Float,
            bits,
            signed: false,
            elements: 0,
            element_type: None,
        }
    }

    /// Create vector type info
    pub const fn vector(element_bits: u8, count: u32) -> Self {
        Self {
            category: SpirvTypeCategory::Vector,
            bits: element_bits,
            signed: false,
            elements: count,
            element_type: None,
        }
    }

    /// Check if this is a numeric type (int or float)
    pub fn is_numeric(&self) -> bool {
        matches!(self.category, SpirvTypeCategory::Int | SpirvTypeCategory::Float)
    }

    /// Check if this is an integer type
    pub fn is_integer(&self) -> bool {
        self.category == SpirvTypeCategory::Int
    }

    /// Check if this is a floating-point type
    pub fn is_float(&self) -> bool {
        self.category == SpirvTypeCategory::Float
    }
}

/// Type mapper for Simple → SPIR-V conversion
///
/// Provides mappings from Simple's TypeId to SPIR-V type information,
/// enabling correct type emission during SPIR-V codegen.
pub struct TypeMapper {
    // No fields needed - all mappings are computed from TypeId constants
}

impl TypeMapper {
    /// Create a new type mapper
    pub fn new() -> Self {
        Self {}
    }

    /// Get SPIR-V type info for a Simple TypeId
    ///
    /// Returns detailed type information needed for SPIR-V codegen.
    pub fn get_type_info(&self, type_id: TypeId) -> Result<SpirvTypeInfo, CompileError> {
        match type_id {
            // Void and bool
            TypeId::VOID => Ok(SpirvTypeInfo::void()),
            TypeId::BOOL => Ok(SpirvTypeInfo::bool()),

            // Signed integers
            TypeId::I8 => Ok(SpirvTypeInfo::signed_int(8)),
            TypeId::I16 => Ok(SpirvTypeInfo::signed_int(16)),
            TypeId::I32 => Ok(SpirvTypeInfo::signed_int(32)),
            TypeId::I64 => Ok(SpirvTypeInfo::signed_int(64)),

            // Unsigned integers
            TypeId::U8 => Ok(SpirvTypeInfo::unsigned_int(8)),
            TypeId::U16 => Ok(SpirvTypeInfo::unsigned_int(16)),
            TypeId::U32 => Ok(SpirvTypeInfo::unsigned_int(32)),
            TypeId::U64 => Ok(SpirvTypeInfo::unsigned_int(64)),

            // Floating point
            TypeId::F32 => Ok(SpirvTypeInfo::float(32)),
            TypeId::F64 => Ok(SpirvTypeInfo::float(64)),

            // String and nil are not supported in SPIR-V
            TypeId::STRING => Err(CompileError::Codegen("String type not supported in SPIR-V".to_string())),
            TypeId::NIL => Err(CompileError::Codegen("Nil type not supported in SPIR-V".to_string())),

            // Custom types need lookup in type registry
            _ => Err(CompileError::Codegen(format!(
                "Unknown type ID {:?} for SPIR-V mapping",
                type_id
            ))),
        }
    }

    /// Get the bit width for a type
    pub fn get_bit_width(&self, type_id: TypeId) -> Option<u8> {
        match type_id {
            TypeId::VOID => Some(0),
            TypeId::BOOL => Some(1),
            TypeId::I8 | TypeId::U8 => Some(8),
            TypeId::I16 | TypeId::U16 => Some(16),
            TypeId::I32 | TypeId::U32 | TypeId::F32 => Some(32),
            TypeId::I64 | TypeId::U64 | TypeId::F64 => Some(64),
            _ => None,
        }
    }

    /// Check if a type is signed (for integers)
    pub fn is_signed(&self, type_id: TypeId) -> Option<bool> {
        match type_id {
            TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 => Some(true),
            TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64 => Some(false),
            _ => None, // Not an integer type
        }
    }

    /// Check if a type is floating-point
    pub fn is_float(&self, type_id: TypeId) -> bool {
        matches!(type_id, TypeId::F32 | TypeId::F64)
    }

    /// Check if a type is integer
    pub fn is_integer(&self, type_id: TypeId) -> bool {
        matches!(
            type_id,
            TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
        )
    }

    /// Check if a type is numeric (int or float)
    pub fn is_numeric(&self, type_id: TypeId) -> bool {
        self.is_integer(type_id) || self.is_float(type_id)
    }

    /// Get the signedness value for SPIR-V OpTypeInt (1 = signed, 0 = unsigned)
    pub fn spirv_signedness(&self, type_id: TypeId) -> u32 {
        if self.is_signed(type_id).unwrap_or(false) {
            1
        } else {
            0
        }
    }

    /// Check if type is supported in SPIR-V
    pub fn is_supported(&self, type_id: TypeId) -> bool {
        !matches!(type_id, TypeId::STRING | TypeId::NIL) && type_id.0 <= TypeId::F64.0
    }
}

impl Default for TypeMapper {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_info_primitives() {
        let mapper = TypeMapper::new();

        // Void
        let info = mapper.get_type_info(TypeId::VOID).unwrap();
        assert_eq!(info.category, SpirvTypeCategory::Void);
        assert_eq!(info.bits, 0);

        // Bool
        let info = mapper.get_type_info(TypeId::BOOL).unwrap();
        assert_eq!(info.category, SpirvTypeCategory::Bool);
        assert_eq!(info.bits, 1);

        // i32
        let info = mapper.get_type_info(TypeId::I32).unwrap();
        assert_eq!(info.category, SpirvTypeCategory::Int);
        assert_eq!(info.bits, 32);
        assert!(info.signed);

        // u64
        let info = mapper.get_type_info(TypeId::U64).unwrap();
        assert_eq!(info.category, SpirvTypeCategory::Int);
        assert_eq!(info.bits, 64);
        assert!(!info.signed);

        // f32
        let info = mapper.get_type_info(TypeId::F32).unwrap();
        assert_eq!(info.category, SpirvTypeCategory::Float);
        assert_eq!(info.bits, 32);
    }

    #[test]
    fn test_bit_width() {
        let mapper = TypeMapper::new();

        assert_eq!(mapper.get_bit_width(TypeId::I8), Some(8));
        assert_eq!(mapper.get_bit_width(TypeId::I16), Some(16));
        assert_eq!(mapper.get_bit_width(TypeId::I32), Some(32));
        assert_eq!(mapper.get_bit_width(TypeId::I64), Some(64));
        assert_eq!(mapper.get_bit_width(TypeId::F32), Some(32));
        assert_eq!(mapper.get_bit_width(TypeId::F64), Some(64));
    }

    #[test]
    fn test_signedness() {
        let mapper = TypeMapper::new();

        assert_eq!(mapper.is_signed(TypeId::I32), Some(true));
        assert_eq!(mapper.is_signed(TypeId::U32), Some(false));
        assert_eq!(mapper.is_signed(TypeId::F32), None); // Not an integer

        assert_eq!(mapper.spirv_signedness(TypeId::I32), 1);
        assert_eq!(mapper.spirv_signedness(TypeId::U32), 0);
    }

    #[test]
    fn test_type_categories() {
        let mapper = TypeMapper::new();

        assert!(mapper.is_integer(TypeId::I32));
        assert!(mapper.is_integer(TypeId::U64));
        assert!(!mapper.is_integer(TypeId::F32));

        assert!(mapper.is_float(TypeId::F32));
        assert!(mapper.is_float(TypeId::F64));
        assert!(!mapper.is_float(TypeId::I32));

        assert!(mapper.is_numeric(TypeId::I32));
        assert!(mapper.is_numeric(TypeId::F64));
        assert!(!mapper.is_numeric(TypeId::BOOL));
    }

    #[test]
    fn test_unsupported_types() {
        let mapper = TypeMapper::new();

        assert!(mapper.get_type_info(TypeId::STRING).is_err());
        assert!(mapper.get_type_info(TypeId::NIL).is_err());

        assert!(!mapper.is_supported(TypeId::STRING));
        assert!(!mapper.is_supported(TypeId::NIL));
        assert!(mapper.is_supported(TypeId::I32));
    }
}
