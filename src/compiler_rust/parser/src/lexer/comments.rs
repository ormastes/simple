use crate::token::{Span, Token, TokenKind};

/// Helper to clean doc comment content by removing leading asterisks.
pub(super) fn clean_doc_comment(content: &str) -> String {
    content
        .lines()
        .map(|line| {
            let trimmed = line.trim();
            if trimmed.starts_with('*') {
                trimmed[1..].trim_start()
            } else {
                trimmed
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_string()
}

impl<'a> super::Lexer<'a> {
    /// Parse nested block comment content with proper depth tracking
    ///
    /// Returns the cleaned comment content. Used for both doc comments
    /// and regular block comments that support nesting.
    pub(super) fn parse_nested_comment(&mut self) -> String {
        let mut content = String::new();
        let mut depth = 1;
        while depth > 0 {
            match self.advance() {
                Some((_, '*')) => {
                    if self.peek() == Some('/') {
                        self.advance(); // consume '/'
                        depth -= 1;
                        if depth > 0 {
                            content.push_str("*/");
                        }
                    } else {
                        content.push('*');
                    }
                }
                Some((_, '/')) => {
                    if self.peek() == Some('*') {
                        self.advance(); // consume '*'
                        depth += 1;
                        content.push_str("/*");
                    } else {
                        content.push('/');
                    }
                }
                Some((_, '\n')) => {
                    self.line += 1;
                    self.column = 1;
                    content.push('\n');
                }
                Some((_, ch)) => {
                    content.push(ch);
                }
                None => break,
            }
        }
        content
    }

    pub(super) fn skip_comment(&mut self) -> TokenKind {
        // Skip until end of line
        while let Some(ch) = self.peek() {
            if ch == '\n' {
                break;
            }
            self.advance();
        }
        // Return next token instead of comment
        self.next_token().kind
    }

    pub(super) fn skip_block_comment(&mut self) -> TokenKind {
        // Skip until */ is found, supporting nested block comments
        let mut depth = 1;
        while depth > 0 {
            match self.advance() {
                Some((_, '*')) => {
                    if self.peek() == Some('/') {
                        self.advance(); // consume '/'
                        depth -= 1;
                    }
                }
                Some((_, '/')) => {
                    if self.peek() == Some('*') {
                        self.advance(); // consume '*'
                        depth += 1;
                    }
                }
                Some((_, '\n')) => {
                    self.line += 1;
                    self.column = 1;
                }
                Some(_) => {}
                None => {
                    // Unterminated block comment - just return next token
                    break;
                }
            }
        }
        // Return next token instead of comment
        self.next_token().kind
    }

    pub(super) fn read_doc_block_comment(&mut self, start_pos: usize, start_line: usize, start_column: usize) -> Token {
        // Read doc comment content until */ is found
        let content = self.parse_nested_comment();
        // Trim leading/trailing whitespace from each line and remove leading *
        let cleaned = clean_doc_comment(&content);

        Token::new(
            TokenKind::DocComment(cleaned),
            Span::new(start_pos, self.current_pos, start_line, start_column),
            self.source[start_pos..self.current_pos].to_string(),
        )
    }

    pub(super) fn read_doc_line_comment(&mut self, start_pos: usize, start_line: usize, start_column: usize) -> Token {
        // Skip leading whitespace after ///
        while let Some(ch) = self.peek() {
            if ch == ' ' || ch == '\t' {
                self.advance();
            } else {
                break;
            }
        }

        // Check if this is a multi-line doc block (/// on its own line)
        if self.peek() == Some('\n') || self.peek().is_none() {
            // This might be a multi-line doc block opener: ///\n...\n///
            return self.read_doc_block_triple_slash(start_pos, start_line, start_column);
        }

        // Single-line doc comment: read until newline
        let mut content = String::new();
        while let Some(ch) = self.peek() {
            if ch == '\n' {
                break;
            }
            content.push(ch);
            self.advance();
        }
        Token::new(
            TokenKind::DocComment(content.trim().to_string()),
            Span::new(start_pos, self.current_pos, start_line, start_column),
            self.source[start_pos..self.current_pos].to_string(),
        )
    }

    /// Read a multi-line doc block delimited by /// on separate lines
    /// Format:
    /// ///
    /// Content line 1
    /// Content line 2
    /// ///
    pub(super) fn read_doc_block_triple_slash(
        &mut self,
        start_pos: usize,
        start_line: usize,
        start_column: usize,
    ) -> Token {
        let mut content = String::new();

        // Consume the opening newline
        if self.peek() == Some('\n') {
            self.advance();
            self.line += 1;
            self.column = 1;
        }

        // Read lines until we find a closing ///
        loop {
            // Check for closing /// at start of line (with optional leading whitespace)
            let line_start_pos = self.current_pos;
            let mut leading_spaces = 0;

            // Skip leading whitespace
            while self.peek() == Some(' ') || self.peek() == Some('\t') {
                self.advance();
                leading_spaces += 1;
            }

            // Check for ///
            if self.peek() == Some('/') {
                self.advance();
                if self.peek() == Some('/') {
                    self.advance();
                    if self.peek() == Some('/') {
                        self.advance();
                        // Check that it's /// followed by newline or whitespace then newline or EOF
                        let mut only_whitespace = true;
                        while let Some(ch) = self.peek() {
                            if ch == '\n' || ch == '\r' {
                                break;
                            } else if ch != ' ' && ch != '\t' {
                                only_whitespace = false;
                                break;
                            }
                            self.advance();
                        }
                        if only_whitespace {
                            // Found closing ///, consume the newline if present
                            if self.peek() == Some('\n') {
                                self.advance();
                                self.line += 1;
                                self.column = 1;
                            }
                            break;
                        } else {
                            // Not a closing ///, this is content
                            // Need to include what we consumed as content
                            content.push_str(&self.source[line_start_pos..self.current_pos]);
                        }
                    } else {
                        // Just // - include as content
                        content.push_str(&self.source[line_start_pos..self.current_pos]);
                    }
                } else {
                    // Just / - include as content
                    content.push_str(&self.source[line_start_pos..self.current_pos]);
                }
            } else {
                // Not a /, restore position and read line normally
                // We need to include the whitespace we skipped
                if leading_spaces > 0 {
                    content.push_str(&" ".repeat(leading_spaces));
                }
            }

            // Read rest of line
            while let Some(ch) = self.peek() {
                if ch == '\n' {
                    content.push('\n');
                    self.advance();
                    self.line += 1;
                    self.column = 1;
                    break;
                }
                content.push(ch);
                self.advance();
            }

            // Check for EOF
            if self.peek().is_none() {
                break;
            }
        }

        // Trim trailing whitespace from content
        let trimmed = content.trim().to_string();

        Token::new(
            TokenKind::DocComment(trimmed),
            Span::new(start_pos, self.current_pos, start_line, start_column),
            self.source[start_pos..self.current_pos].to_string(),
        )
    }
}
