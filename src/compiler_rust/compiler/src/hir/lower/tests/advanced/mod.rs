// Advanced HIR lowering tests - SIMD and GPU intrinsics
//
// This module contains tests for advanced features:
// - SIMD vector operations and intrinsics
// - GPU compute intrinsics and atomic operations
// - Thread group operations and barriers
// - Vector swizzling and shuffling
// - Memory operations (load/store/gather/scatter)

use super::super::super::types::*;
use super::super::*;
use simple_parser::Parser;

/// Helper function to parse source and lower to HIR
pub(super) fn parse_and_lower(source: &str) -> LowerResult<HirModule> {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");
    lower(&module)
}

// Test modules organized by functionality
mod gpu_ops;
mod simd_intrinsics;
mod simd_memory;
mod simd_swizzle;
mod simd_vectors;
