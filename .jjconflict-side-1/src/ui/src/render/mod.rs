//! Renderer abstraction and TUI implementation
//!
//! Provides the `RenderBackend` trait and TUI renderer.

mod backend;
mod tui;

pub use backend::*;
pub use tui::*;
