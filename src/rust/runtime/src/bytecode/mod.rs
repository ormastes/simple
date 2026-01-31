//! Bytecode execution system for Simple Module Format (SMF) files.
//!
//! This module provides a stack-based bytecode virtual machine for executing
//! Simple programs compiled to bytecode. It sits between the interpreter
//! (slow, development) and native code (fast, production) modes.
//!
//! **Performance Targets:**
//! - Interpreter: 1x (baseline)
//! - Bytecode: 5-10x faster than interpreter
//! - Native (Cranelift): 50-100x faster than interpreter
//!
//! **Key Components:**
//! - `opcodes`: Instruction set definitions and encoding
//! - `vm`: Stack-based execution engine
//! - `disassembler`: Debugging and inspection tools (Phase 3)
//!
//! **Architecture:**
//! ```text
//! ┌─────────────┐
//! │  MIR Code   │
//! └─────┬───────┘
//!       │
//!       ▼
//! ┌─────────────────┐
//! │ Bytecode        │
//! │ Compiler        │
//! └─────┬───────────┘
//!       │
//!       ▼
//! ┌─────────────────┐
//! │ SMF File        │
//! │ (Code Section)  │
//! └─────┬───────────┘
//!       │
//!       ▼
//! ┌─────────────────┐
//! │ Bytecode VM     │
//! │ (This Module)   │
//! └─────────────────┘
//! ```

pub mod opcodes;
pub mod vm;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod vm_tests;
