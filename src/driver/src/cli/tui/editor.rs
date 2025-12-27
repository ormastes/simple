//! Line editor implementation with smart indent handling
//!
//! This editor provides:
//! - Smart backspace: deletes 4 spaces when in leading whitespace
//! - Automatic indentation after ':' (Python-style)
//! - Cursor movement and text insertion
//! - Multi-line input support

use super::keybindings::EditorAction;

/// Line editor state
#[derive(Debug, Clone)]
pub struct LineEditor {
    /// Current line content
    buffer: String,
    /// Cursor position (byte offset)
    cursor: usize,
    /// Accumulated lines for multi-line input
    lines: Vec<String>,
    /// Whether we're in multi-line mode
    in_multiline: bool,
    /// Debug logging enabled
    debug_mode: bool,
}

impl LineEditor {
    /// Create a new line editor
    pub fn new() -> Self {
        Self {
            buffer: String::new(),
            cursor: 0,
            lines: Vec::new(),
            in_multiline: false,
            debug_mode: false,
        }
    }

    /// Enable debug logging
    pub fn set_debug_mode(&mut self, enabled: bool) {
        self.debug_mode = enabled;
    }

    /// Get the current line content
    pub fn buffer(&self) -> &str {
        &self.buffer
    }

    /// Get the cursor position
    pub fn cursor(&self) -> usize {
        self.cursor
    }

    /// Get accumulated lines
    pub fn lines(&self) -> &[String] {
        &self.lines
    }

    /// Check if in multi-line mode
    pub fn is_multiline(&self) -> bool {
        self.in_multiline
    }

    /// Reset the editor state
    pub fn reset(&mut self) {
        self.buffer.clear();
        self.cursor = 0;
        self.lines.clear();
        self.in_multiline = false;
    }

    /// Apply an action to the editor
    pub fn apply_action(&mut self, action: EditorAction) -> EditorResult {
        match action {
            EditorAction::InsertChar(c) => {
                let old_cap = self.buffer.capacity();
                let old_len = self.buffer.len();

                if self.debug_mode {
                    eprintln!("[DEBUG] InsertChar '{}': before len={}, cap={}",
                              c, old_len, old_cap);
                }

                self.buffer.insert(self.cursor, c);
                self.cursor += c.len_utf8();

                if self.debug_mode {
                    let new_cap = self.buffer.capacity();
                    let new_len = self.buffer.len();
                    eprintln!("[DEBUG]   after len={}, cap={}, reallocated={}",
                              new_len, new_cap, new_cap != old_cap);
                }

                EditorResult::Continue
            }

            EditorAction::InsertIndent => {
                let old_cap = self.buffer.capacity();
                let old_len = self.buffer.len();

                if self.debug_mode {
                    eprintln!("[DEBUG] InsertIndent: before len={}, cap={}",
                              old_len, old_cap);
                }

                self.buffer.insert_str(self.cursor, "    ");
                self.cursor += 4;

                if self.debug_mode {
                    let new_cap = self.buffer.capacity();
                    let new_len = self.buffer.len();
                    eprintln!("[DEBUG]   after len={}, cap={}, reallocated={}",
                              new_len, new_cap, new_cap != old_cap);
                }

                EditorResult::Continue
            }

            EditorAction::Backspace => {
                if self.cursor > 0 {
                    let old_cap = self.buffer.capacity();
                    let old_len = self.buffer.len();
                    let before_cursor = &self.buffer[..self.cursor];

                    if self.debug_mode {
                        eprintln!("[DEBUG] Backspace: cursor={}, buffer='{}', len={}, cap={}",
                                  self.cursor, self.buffer, old_len, old_cap);
                        eprintln!("[DEBUG]   before_cursor='{}'", before_cursor);
                    }

                    // Check if we're in leading whitespace (Python-style smart backspace)
                    if before_cursor.chars().all(|c| c == ' ') && !before_cursor.is_empty() {
                        // Delete full indent (4 spaces or all remaining)
                        let spaces_to_delete = if before_cursor.len() >= 4 {
                            4
                        } else {
                            before_cursor.len()
                        };

                        // Check if buffer has content after cursor (not just leading spaces)
                        let has_content_after = self.cursor < self.buffer.len();
                        let would_be_empty = !has_content_after && self.buffer.len() == spaces_to_delete;

                        if self.debug_mode {
                            eprintln!("[DEBUG]   In leading whitespace: deleting {} spaces", spaces_to_delete);
                            eprintln!("[DEBUG]   has_content_after={}, would_be_empty={}",
                                      has_content_after, would_be_empty);
                        }

                        // If deleting would leave buffer empty, just delete 1 space instead
                        let spaces_to_delete = if would_be_empty {
                            if self.debug_mode {
                                eprintln!("[DEBUG]   Would be empty, deleting only 1 space");
                            }
                            1
                        } else {
                            spaces_to_delete
                        };

                        if self.debug_mode && !would_be_empty {
                            eprintln!("[DEBUG]   Proceeding with {} space deletion", spaces_to_delete);
                        }

                        // Remove the spaces
                        for _ in 0..spaces_to_delete {
                            if self.cursor > 0 {
                                let prev_char_idx = self.buffer[..self.cursor]
                                    .char_indices()
                                    .next_back()
                                    .map(|(idx, _)| idx)
                                    .unwrap_or(0);
                                self.buffer.remove(prev_char_idx);
                                self.cursor = prev_char_idx;
                            }
                        }

                        if self.debug_mode {
                            let new_cap = self.buffer.capacity();
                            let new_len = self.buffer.len();
                            eprintln!("[DEBUG]   After deletion: cursor={}, buffer='{}', len={}, cap={}, reallocated={}",
                                      self.cursor, self.buffer, new_len, new_cap, new_cap != old_cap);
                        }
                    } else {
                        if self.debug_mode {
                            eprintln!("[DEBUG]   Not in leading whitespace: deleting 1 char");
                        }

                        // Delete single character
                        let prev_char_idx = self.buffer[..self.cursor]
                            .char_indices()
                            .next_back()
                            .map(|(idx, _)| idx)
                            .unwrap_or(0);
                        self.buffer.remove(prev_char_idx);
                        self.cursor = prev_char_idx;

                        if self.debug_mode {
                            let new_cap = self.buffer.capacity();
                            let new_len = self.buffer.len();
                            eprintln!("[DEBUG]   After deletion: cursor={}, buffer='{}', len={}, cap={}, reallocated={}",
                                      self.cursor, self.buffer, new_len, new_cap, new_cap != old_cap);
                        }
                    }
                }
                EditorResult::Continue
            }

            EditorAction::Delete => {
                if self.cursor < self.buffer.len() {
                    self.buffer.remove(self.cursor);
                }
                EditorResult::Continue
            }

            EditorAction::DeleteIndent => {
                // Delete from start of line to cursor (like Ctrl+U in bash)
                if self.cursor > 0 {
                    let before_cursor = &self.buffer[..self.cursor];
                    let spaces_count = before_cursor.chars().take_while(|&c| c == ' ').count();

                    if spaces_count > 0 {
                        // Delete up to 4 leading spaces
                        let to_delete = spaces_count.min(4);
                        for _ in 0..to_delete {
                            if !self.buffer.is_empty() && self.cursor > 0 {
                                self.buffer.remove(0);
                                self.cursor -= 1;
                            }
                        }
                    } else {
                        // Not in leading whitespace, delete to start of line
                        self.buffer.drain(..self.cursor);
                        self.cursor = 0;
                    }
                }
                EditorResult::Continue
            }

            EditorAction::MoveLeft => {
                if self.cursor > 0 {
                    let prev_char_idx = self.buffer[..self.cursor]
                        .char_indices()
                        .next_back()
                        .map(|(idx, _)| idx)
                        .unwrap_or(0);
                    self.cursor = prev_char_idx;
                }
                EditorResult::Continue
            }

            EditorAction::MoveRight => {
                if self.cursor < self.buffer.len() {
                    let next_char_idx = self.buffer[self.cursor..]
                        .char_indices()
                        .nth(1)
                        .map(|(idx, _)| self.cursor + idx)
                        .unwrap_or(self.buffer.len());
                    self.cursor = next_char_idx;
                }
                EditorResult::Continue
            }

            EditorAction::MoveHome => {
                self.cursor = 0;
                EditorResult::Continue
            }

            EditorAction::MoveEnd => {
                self.cursor = self.buffer.len();
                EditorResult::Continue
            }

            EditorAction::AcceptLine => {
                let line = self.buffer.clone();
                self.lines.push(line.clone());

                // Check if we need continuation
                if line.trim_end().ends_with(':') || self.has_unbalanced_brackets() {
                    // Line ends with ':' or has unbalanced brackets - enter/stay in multiline
                    self.in_multiline = true;

                    // Calculate auto-indent level
                    let auto_indent = self.calculate_auto_indent(&line);

                    if self.debug_mode {
                        eprintln!("[DEBUG] AcceptLine: Entering/staying in multiline mode");
                        eprintln!("[DEBUG]   Previous line: '{}'", line);
                        eprintln!("[DEBUG]   Auto-indent: {} spaces", auto_indent.len());
                    }

                    // Set buffer to auto-indent
                    self.buffer = auto_indent;
                    self.cursor = self.buffer.len();

                    EditorResult::Continue
                } else if self.in_multiline {
                    // Already in multiline mode
                    if line.trim().is_empty() {
                        // Empty line - complete the block and execute
                        if self.debug_mode {
                            eprintln!("[DEBUG] AcceptLine: Empty line in multiline - completing block");
                        }
                        let full_input = self.lines.join("\n");
                        self.reset();
                        EditorResult::Accepted(full_input)
                    } else {
                        // Non-empty line - stay in multiline mode
                        // Calculate indent (dedent if needed)
                        let auto_indent = self.calculate_auto_indent(&line);

                        if self.debug_mode {
                            eprintln!("[DEBUG] AcceptLine: Staying in multiline mode");
                            eprintln!("[DEBUG]   Previous line: '{}'", line);
                            eprintln!("[DEBUG]   Auto-indent: {} spaces", auto_indent.len());
                        }

                        self.buffer = auto_indent;
                        self.cursor = self.buffer.len();

                        EditorResult::Continue
                    }
                } else {
                    // Single line complete - not in multiline mode
                    if self.debug_mode {
                        eprintln!("[DEBUG] AcceptLine: Single line complete");
                    }
                    let full_input = self.lines.join("\n");
                    self.reset();
                    EditorResult::Accepted(full_input)
                }
            }

            EditorAction::Cancel => {
                self.reset();
                EditorResult::Cancelled
            }

            EditorAction::Exit => EditorResult::Exit,

            EditorAction::None => EditorResult::Continue,
        }
    }

    /// Check if accumulated lines have unbalanced brackets
    fn has_unbalanced_brackets(&self) -> bool {
        let text = self.lines.join("\n");
        let mut paren = 0i32;
        let mut bracket = 0i32;
        let mut brace = 0i32;
        let mut in_string = false;
        let mut escape_next = false;

        for ch in text.chars() {
            if escape_next {
                escape_next = false;
                continue;
            }
            if ch == '\\' && in_string {
                escape_next = true;
                continue;
            }
            if ch == '"' {
                in_string = !in_string;
                continue;
            }
            if in_string {
                continue;
            }
            match ch {
                '(' => paren += 1,
                ')' => paren -= 1,
                '[' => bracket += 1,
                ']' => bracket -= 1,
                '{' => brace += 1,
                '}' => brace -= 1,
                _ => {}
            }
        }
        paren > 0 || bracket > 0 || brace > 0
    }

    /// Calculate automatic indentation level for next line
    /// Returns a string of spaces for the appropriate indent level
    fn calculate_auto_indent(&self, line: &str) -> String {
        // Get existing indentation from the line
        let existing_indent = line.chars().take_while(|&c| c == ' ').count();

        // If line ends with ':', add one more indent level (4 spaces)
        if line.trim_end().ends_with(':') {
            " ".repeat(existing_indent + 4)
        } else {
            // Keep same indent level
            " ".repeat(existing_indent)
        }
    }
}

impl Default for LineEditor {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of applying an action to the editor
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EditorResult {
    /// Continue editing
    Continue,
    /// Line accepted (complete input)
    Accepted(String),
    /// Input cancelled (Ctrl+C)
    Cancelled,
    /// Exit REPL (Ctrl+D)
    Exit,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_char() {
        let mut editor = LineEditor::new();
        editor.apply_action(EditorAction::InsertChar('a'));
        assert_eq!(editor.buffer(), "a");
        assert_eq!(editor.cursor(), 1);
    }

    #[test]
    fn test_insert_indent() {
        let mut editor = LineEditor::new();
        editor.apply_action(EditorAction::InsertIndent);
        assert_eq!(editor.buffer(), "    ");
        assert_eq!(editor.cursor(), 4);
    }

    #[test]
    fn test_backspace_deletes_full_indent_with_prevention() {
        let mut editor = LineEditor::new();
        // Insert 4 spaces
        editor.apply_action(EditorAction::InsertIndent);
        assert_eq!(editor.buffer(), "    ");
        assert_eq!(editor.cursor(), 4);

        // Backspace should delete only 1 space (empty buffer prevention)
        // When buffer would become empty, only delete 1 space instead of 4
        editor.apply_action(EditorAction::Backspace);
        assert_eq!(editor.buffer(), "   ", "Should leave 3 spaces (empty buffer prevention)");
        assert_eq!(editor.cursor(), 3);
    }

    #[test]
    fn test_backspace_deletes_partial_indent_with_prevention() {
        let mut editor = LineEditor::new();
        // Insert 2 spaces
        editor.apply_action(EditorAction::InsertChar(' '));
        editor.apply_action(EditorAction::InsertChar(' '));
        assert_eq!(editor.buffer(), "  ");
        assert_eq!(editor.cursor(), 2);

        // Backspace should delete only 1 space (empty buffer prevention)
        editor.apply_action(EditorAction::Backspace);
        assert_eq!(editor.buffer(), " ", "Should leave 1 space (empty buffer prevention)");
        assert_eq!(editor.cursor(), 1);
    }

    #[test]
    fn test_backspace_after_text_deletes_one_char() {
        let mut editor = LineEditor::new();
        // Insert indent + text
        editor.apply_action(EditorAction::InsertIndent);
        editor.apply_action(EditorAction::InsertChar('h'));
        editor.apply_action(EditorAction::InsertChar('i'));
        assert_eq!(editor.buffer(), "    hi");
        assert_eq!(editor.cursor(), 6);

        // Backspace should delete only 'i'
        editor.apply_action(EditorAction::Backspace);
        assert_eq!(editor.buffer(), "    h");
        assert_eq!(editor.cursor(), 5);
    }

    #[test]
    fn test_backspace_deletes_4_spaces_with_text_after() {
        let mut editor = LineEditor::new();
        // Insert 8 spaces + text
        editor.apply_action(EditorAction::InsertIndent);
        editor.apply_action(EditorAction::InsertIndent);
        editor.apply_action(EditorAction::InsertChar('x'));
        assert_eq!(editor.buffer(), "        x");
        assert_eq!(editor.cursor(), 9);

        // Move cursor back to position 8 (after 8 spaces, before 'x')
        editor.apply_action(EditorAction::MoveLeft);
        assert_eq!(editor.cursor(), 8);

        // Backspace should delete 4 spaces (smart backspace, has content after)
        editor.apply_action(EditorAction::Backspace);
        assert_eq!(editor.buffer(), "    x", "Should delete 4 spaces when content after cursor");
        assert_eq!(editor.cursor(), 4);
    }

    #[test]
    fn test_cursor_movement() {
        let mut editor = LineEditor::new();
        editor.apply_action(EditorAction::InsertChar('a'));
        editor.apply_action(EditorAction::InsertChar('b'));
        editor.apply_action(EditorAction::InsertChar('c'));
        assert_eq!(editor.cursor(), 3);

        editor.apply_action(EditorAction::MoveLeft);
        assert_eq!(editor.cursor(), 2);

        editor.apply_action(EditorAction::MoveHome);
        assert_eq!(editor.cursor(), 0);

        editor.apply_action(EditorAction::MoveEnd);
        assert_eq!(editor.cursor(), 3);
    }

    #[test]
    fn test_auto_indentation_after_colon() {
        println!("\n=== TEST: Auto-indentation after ':' ===");

        let mut editor = LineEditor::new();

        // Type "if x > 0:" and press Enter
        editor.apply_action(EditorAction::InsertChar('i'));
        editor.apply_action(EditorAction::InsertChar('f'));
        editor.apply_action(EditorAction::InsertChar(' '));
        editor.apply_action(EditorAction::InsertChar('x'));
        editor.apply_action(EditorAction::InsertChar(' '));
        editor.apply_action(EditorAction::InsertChar('>'));
        editor.apply_action(EditorAction::InsertChar(' '));
        editor.apply_action(EditorAction::InsertChar('0'));
        editor.apply_action(EditorAction::InsertChar(':'));

        println!("Before Enter:");
        println!("  buffer: '{}'", editor.buffer());
        println!("  in_multiline: {}", editor.is_multiline());

        // Press Enter - should enter multiline mode WITH auto-indent
        let result = editor.apply_action(EditorAction::AcceptLine);

        println!("\nAfter Enter:");
        println!("  result: {:?}", result);
        println!("  buffer: '{}'", editor.buffer());
        println!("  buffer.len(): {}", editor.buffer().len());
        println!("  cursor: {}", editor.cursor());
        println!("  in_multiline: {}", editor.is_multiline());
        println!("  lines: {:?}", editor.lines());

        // Verify auto-indent is present
        assert_eq!(result, EditorResult::Continue, "Should continue in multiline mode");
        assert!(editor.is_multiline(), "Should be in multiline mode");
        assert_eq!(editor.buffer(), "    ", "Buffer should have 4 spaces for auto-indent");
        assert_eq!(editor.cursor(), 4, "Cursor should be at position 4");

        println!("\n✅ PASS: Auto-indentation is working!");
    }

    #[test]
    fn test_nested_auto_indentation() {
        println!("\n=== TEST: Nested auto-indentation ===");

        let mut editor = LineEditor::new();

        // First level: "if x > 0:"
        for c in "if x > 0:".chars() {
            editor.apply_action(EditorAction::InsertChar(c));
        }
        editor.apply_action(EditorAction::AcceptLine);

        println!("After first Enter:");
        println!("  buffer: '{}'", editor.buffer());
        println!("  buffer.len(): {}", editor.buffer().len());

        assert_eq!(editor.buffer(), "    ", "Should have 4 spaces");

        // Second level: "if y > 0:"
        for c in "if y > 0:".chars() {
            editor.apply_action(EditorAction::InsertChar(c));
        }

        println!("\nBefore second Enter:");
        println!("  buffer: '{}'", editor.buffer());

        editor.apply_action(EditorAction::AcceptLine);

        println!("\nAfter second Enter:");
        println!("  buffer: '{}'", editor.buffer());
        println!("  buffer.len(): {}", editor.buffer().len());

        assert_eq!(editor.buffer(), "        ", "Should have 8 spaces (4 + 4)");
        assert_eq!(editor.cursor(), 8, "Cursor should be at position 8");

        println!("\n✅ PASS: Nested indentation is working!");
    }

    #[test]
    fn test_multiline_stays_active_on_non_colon_line() {
        println!("\n=== TEST: Multiline stays active after non-colon line ===");

        let mut editor = LineEditor::new();

        // Line 1: "if 1:"
        for c in "if 1:".chars() {
            editor.apply_action(EditorAction::InsertChar(c));
        }
        let result1 = editor.apply_action(EditorAction::AcceptLine);

        println!("After 'if 1:' + Enter:");
        println!("  result: {:?}", result1);
        println!("  in_multiline: {}", editor.is_multiline());
        println!("  buffer: '{}'", editor.buffer());

        assert_eq!(result1, EditorResult::Continue);
        assert!(editor.is_multiline(), "Should be in multiline mode");
        assert_eq!(editor.buffer(), "    ");

        // Line 2: "    if 1:"
        for c in "if 1:".chars() {
            editor.apply_action(EditorAction::InsertChar(c));
        }
        let result2 = editor.apply_action(EditorAction::AcceptLine);

        println!("\nAfter '    if 1:' + Enter:");
        println!("  result: {:?}", result2);
        println!("  in_multiline: {}", editor.is_multiline());
        println!("  buffer: '{}'", editor.buffer());

        assert_eq!(result2, EditorResult::Continue);
        assert!(editor.is_multiline(), "Should stay in multiline mode");
        assert_eq!(editor.buffer(), "        ");

        // Line 3: "        print 1" (no colon - should STAY in multiline!)
        for c in "print 1".chars() {
            editor.apply_action(EditorAction::InsertChar(c));
        }
        let result3 = editor.apply_action(EditorAction::AcceptLine);

        println!("\nAfter '        print 1' + Enter:");
        println!("  result: {:?}", result3);
        println!("  in_multiline: {}", editor.is_multiline());
        println!("  buffer: '{}'", editor.buffer());

        // Should STAY in multiline mode because we're already in a block
        assert_eq!(result3, EditorResult::Continue, "Should stay in multiline mode");
        assert!(editor.is_multiline(), "Should still be in multiline mode");

        // Line 4: Empty line - should complete the block
        let result4 = editor.apply_action(EditorAction::AcceptLine);

        println!("\nAfter empty line + Enter:");
        println!("  result: {:?}", result4);
        println!("  in_multiline: {}", editor.is_multiline());

        // Now should execute
        assert!(matches!(result4, EditorResult::Accepted(_)), "Should execute on empty line");
        assert!(!editor.is_multiline(), "Should have exited multiline mode");

        println!("\n✅ PASS: Multiline mode stays active correctly!");
    }
}
