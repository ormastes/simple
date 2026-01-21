//! Keybindings using crossterm
//!
//! This module defines the keybindings for the TUI REPL, including:
//! - Backspace deletes full indent (4 spaces) when in leading whitespace
//! - Ctrl+U deletes full indent
//! - Tab inserts 4 spaces
//! - Standard editing keys (arrows, home, end, etc.)

use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

/// Action that can be triggered by a key combination
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EditorAction {
    /// Insert 4 spaces (Tab)
    InsertIndent,
    /// Delete 4 spaces or to start of line (Ctrl+U)
    DeleteIndent,
    /// Delete character before cursor (or full indent if in leading whitespace)
    Backspace,
    /// Delete character after cursor
    Delete,
    /// Move cursor left
    MoveLeft,
    /// Move cursor right
    MoveRight,
    /// Move to start of line
    MoveHome,
    /// Move to end of line
    MoveEnd,
    /// Accept line (Enter)
    AcceptLine,
    /// Cancel input (Ctrl+C)
    Cancel,
    /// Exit REPL (Ctrl+D)
    Exit,
    /// Insert character
    InsertChar(char),
    /// No action (ignore key)
    None,
}

/// Keybinding configuration for the TUI REPL
pub struct KeyBindings {}

impl KeyBindings {
    /// Create default keybindings
    pub fn new() -> Self {
        Self {}
    }

    /// Get action for a key event
    pub fn get_action(&self, key: KeyEvent) -> EditorAction {
        // Debug: log key events for Tab and Backspace
        if std::env::var("TUI_DEBUG").is_ok() {
            match key.code {
                KeyCode::Tab => eprintln!("[DEBUG] Key received: Tab"),
                KeyCode::Backspace => eprintln!("[DEBUG] Key received: Backspace"),
                _ => {}
            }
        }

        match (key.code, key.modifiers) {
            // Tab → Insert 4 spaces
            (KeyCode::Tab, _) => EditorAction::InsertIndent,

            // Backspace → Smart delete (4 spaces if in indent, else 1 char)
            (KeyCode::Backspace, KeyModifiers::NONE) => EditorAction::Backspace,

            // Delete → Delete char after cursor
            (KeyCode::Delete, _) => EditorAction::Delete,

            // Ctrl+U → Delete indent or to start of line
            (KeyCode::Char('u'), mods) | (KeyCode::Char('U'), mods) if mods.contains(KeyModifiers::CONTROL) => {
                EditorAction::DeleteIndent
            }

            // Ctrl+C → Cancel
            (KeyCode::Char('c'), mods) | (KeyCode::Char('C'), mods) if mods.contains(KeyModifiers::CONTROL) => {
                EditorAction::Cancel
            }

            // Ctrl+D → Exit
            (KeyCode::Char('d'), mods) | (KeyCode::Char('D'), mods) if mods.contains(KeyModifiers::CONTROL) => {
                EditorAction::Exit
            }

            // Enter → Accept line
            (KeyCode::Enter, _) => EditorAction::AcceptLine,

            // Arrow keys
            (KeyCode::Left, _) => EditorAction::MoveLeft,
            (KeyCode::Right, _) => EditorAction::MoveRight,
            (KeyCode::Home, _) => EditorAction::MoveHome,
            (KeyCode::End, _) => EditorAction::MoveEnd,

            // Regular characters
            (KeyCode::Char(c), KeyModifiers::NONE) | (KeyCode::Char(c), KeyModifiers::SHIFT) => {
                EditorAction::InsertChar(c)
            }

            // Ignore other keys
            _ => EditorAction::None,
        }
    }
}

impl Default for KeyBindings {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tab_inserts_indent() {
        let bindings = KeyBindings::new();
        let key = KeyEvent::new(KeyCode::Tab, KeyModifiers::NONE);
        assert_eq!(bindings.get_action(key), EditorAction::InsertIndent);
    }

    #[test]
    fn test_backspace() {
        let bindings = KeyBindings::new();
        let key = KeyEvent::new(KeyCode::Backspace, KeyModifiers::NONE);
        assert_eq!(bindings.get_action(key), EditorAction::Backspace);
    }

    #[test]
    fn test_ctrl_u_deletes_indent() {
        let bindings = KeyBindings::new();
        let key = KeyEvent::new(KeyCode::Char('u'), KeyModifiers::CONTROL);
        assert_eq!(bindings.get_action(key), EditorAction::DeleteIndent);
    }

    #[test]
    fn test_enter_accepts_line() {
        let bindings = KeyBindings::new();
        let key = KeyEvent::new(KeyCode::Enter, KeyModifiers::NONE);
        assert_eq!(bindings.get_action(key), EditorAction::AcceptLine);
    }

    #[test]
    fn test_char_insertion() {
        let bindings = KeyBindings::new();
        let key = KeyEvent::new(KeyCode::Char('a'), KeyModifiers::NONE);
        assert_eq!(bindings.get_action(key), EditorAction::InsertChar('a'));
    }
}
