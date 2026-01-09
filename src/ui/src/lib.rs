//! Simple UI Framework - Rust Components
//!
//! This crate provides the SUI template parser and FFI for the Simple language.
//! The actual UI framework (Element types, PatchSet, rendering) is implemented
//! in Simple stdlib at `simple/std_lib/src/ui/`.
//!
//! # Architecture
//!
//! ```text
//! .sui file → SuiLexer → SuiParser → TemplateAST → IR
//!                                                   ↓
//!                                          Simple stdlib ui/
//!                                     (Element, PatchSet, Renderer)
//! ```
//!
//! # Rust Components (this crate)
//!
//! - **lexer/**: SUI template tokenization
//! - **parser/**: SUI template parsing to AST
//! - **ir/**: Intermediate representations for compiler
//! - **ffi/**: Minimal FFI for TUI/GUI primitives
//!
//! # Simple Components (stdlib)
//!
//! - **ui/element.spl**: Shared Element/Node types
//! - **ui/patchset.spl**: PatchOp types and diff algorithm
//! - **ui/renderer.spl**: RenderBackend trait
//! - **ui/tui/**: TUI renderer implementation
//! - **ui/gui/**: GUI renderer implementation (future)

pub mod ffi;
pub mod ir;
pub mod lexer;
pub mod parser;

// Keep patchset/render for reference during transition
pub mod hydration;
pub mod patchset;
pub mod render;
pub mod ssr;

// Re-export main types for compiler integration
pub use ir::{InitIR, RenderIR, TemplateIR};
pub use lexer::{SuiLexer, SuiToken, SuiTokenKind};
pub use parser::{SuiParser, SuiTemplate, TemplateNode};
