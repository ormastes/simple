// Common test helpers
use super::*;
use simple_parser::Parser;

/// Parse Simple source and lower to HIR
pub fn parse_and_lower(source: &str) -> LowerResult<HirModule> {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");
    lower(&module)
}

// Test modules
mod advanced; // Refactored into sub-modules (SIMD/GPU tests)
mod class_tests;
mod control_flow_tests;
mod expression_tests;
mod function_tests;
mod lifetime_tests;
