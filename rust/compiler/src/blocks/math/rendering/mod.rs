//! Math expression rendering to multiple output formats.
//!
//! Supports:
//! - MathML: XML-based math markup for web
//! - Unicode text: Human-readable text with Unicode math symbols
//! - Lean4: Lean theorem prover syntax

pub mod mathml;
pub mod unicode_text;
pub mod lean;
