//! Type mapping from Simple to SPIR-V
//!
//! Maps Simple language types to their SPIR-V equivalents.

use crate::error::CompileError;

/// Type mapper for Simple → SPIR-V conversion
pub struct TypeMapper {
    // TODO: [codegen][P3] Add type ID mappings
}

impl TypeMapper {
    /// Create a new type mapper
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for TypeMapper {
    fn default() -> Self {
        Self::new()
    }
}
