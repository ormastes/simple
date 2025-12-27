//! TUI-based REPL using crossterm + ratatui + crokey
//!
//! This module provides an alternative to the rustyline-based REPL with:
//! - Full control over key handling (no rustyline limitations)
//! - Configurable keybindings via crokey
//! - Backspace can delete full indent levels (4 spaces)
//! - Modern TUI framework (ratatui)
//!
//! Enabled with the 'tui' feature flag.

#[cfg(feature = "tui")]
pub mod editor;
#[cfg(feature = "tui")]
pub mod keybindings;
#[cfg(feature = "tui")]
pub mod repl;

#[cfg(feature = "tui")]
pub use repl::run_tui_repl;
