//! Render mode control for block display output.
//!
//! Controls how custom blocks (math, lean, etc.) are rendered:
//! - `Plain`: ASCII-only output for logging, CI, plain terminals
//! - `Unicode`: Unicode characters (default) for terminal display
//! - `Rich`: Structured JSON metadata for editor plugins (LSP)

use std::cell::Cell;

/// Rendering mode for block display
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RenderMode {
    /// ASCII-only output (e.g., `x^2 + y^2`)
    Plain,
    /// Unicode characters (e.g., `x² + y²`, `√`, `∑`, `α`) — default
    Unicode,
    /// Structured JSON metadata for editor plugins
    Rich,
}

impl Default for RenderMode {
    fn default() -> Self {
        RenderMode::Unicode
    }
}

thread_local! {
    static RENDER_MODE: Cell<RenderMode> = Cell::new(RenderMode::Unicode);
}

/// Get the current render mode
pub fn current_render_mode() -> RenderMode {
    RENDER_MODE.with(|cell| cell.get())
}

/// Set the render mode for the current thread
pub fn set_render_mode(mode: RenderMode) {
    RENDER_MODE.with(|cell| cell.set(mode));
}

/// Execute a closure with a specific render mode, restoring the previous mode after
pub fn with_render_mode<F, R>(mode: RenderMode, f: F) -> R
where
    F: FnOnce() -> R,
{
    let prev = current_render_mode();
    set_render_mode(mode);
    let result = f();
    set_render_mode(prev);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_is_unicode() {
        assert_eq!(current_render_mode(), RenderMode::Unicode);
    }

    #[test]
    fn test_set_and_get() {
        set_render_mode(RenderMode::Plain);
        assert_eq!(current_render_mode(), RenderMode::Plain);
        set_render_mode(RenderMode::Unicode); // restore
    }

    #[test]
    fn test_with_render_mode() {
        set_render_mode(RenderMode::Unicode);
        with_render_mode(RenderMode::Rich, || {
            assert_eq!(current_render_mode(), RenderMode::Rich);
        });
        assert_eq!(current_render_mode(), RenderMode::Unicode);
    }
}
