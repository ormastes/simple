//! Consolidated contract tests
//!
//! This test suite consolidates all contract-related tests from:
//! - Parser (contract syntax parsing)
//! - Compiler MIR (contract lowering)
//! - Runtime (contract verification)
//!
//! Tests cover:
//! - requires: blocks (preconditions)
//! - ensures: blocks (postconditions)
//! - invariant: blocks (class invariants)
//! - old(expr) expressions
//! - Contract modes (verification levels)

mod common;
mod parser_tests;
mod mir_tests;
mod contract_modes;
mod runtime_tests;
