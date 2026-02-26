//! Statement parsing module
//!
//! This module contains all statement parsing logic including:
//! - Variable declarations (let, mut let, const, static)
//! - Control flow (if, for, while, loop, match)
//! - Jump statements (return, break, continue)
//! - Assert statements (assert, check) - inline contract checks
//! - Context and with statements
//! - Contract blocks (requires/ensures/invariant) - LLM-friendly feature #400
//! - Gherkin-style system test DSL (feature/scenario/examples) - Features #606-610
//! - Module system (use, import, mod, export)
//! - Macro definitions
//! - AOP and bounds

mod aop;
mod asm;
mod assert;
mod bounds;
mod contract;
mod control_flow;
mod gherkin;
mod jump;
mod lean;
mod macro_parsing;
mod module_system;
mod unit_parsing;
mod var_decl;

// Re-export specific statement parsing methods if needed
// (Most are already pub(crate) in their respective modules)
