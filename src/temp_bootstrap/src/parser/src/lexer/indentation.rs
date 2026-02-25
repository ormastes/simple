use crate::token::{Span, Token, TokenKind};

use super::comments::clean_doc_comment;

impl<'a> super::Lexer<'a> {
    /// Process indentation change and return the token that should be emitted
    /// along with any additional token. If there is an indent/dedent change,
    /// the indent/dedent token(s) are queued in pending_tokens and the
    /// extra_token (if any) is also queued, so the caller can return the first one.
    /// Returns the token to return from handle_indentation.
    fn emit_with_indentation(
        &mut self,
        indent: usize,
        start_pos: usize,
        start_line: usize,
        extra_token: Token,
    ) -> Option<Token> {
        let current_indent = *self.indent_stack.last().unwrap_or(&0);

        if indent > current_indent {
            // Need to emit INDENT first, then the extra token
            self.indent_stack.push(indent);
            // Push extra_token to pending so it comes after INDENT
            self.pending_tokens.push(extra_token);
            Some(Token::new(
                TokenKind::Indent,
                Span::new(start_pos, self.current_pos, start_line, 1),
                String::new(),
            ))
        } else if indent < current_indent {
            // Generate DEDENT tokens
            while let Some(&top) = self.indent_stack.last() {
                if top <= indent {
                    break;
                }
                self.indent_stack.pop();
                self.pending_tokens.push(Token::new(
                    TokenKind::Dedent,
                    Span::new(start_pos, self.current_pos, start_line, 1),
                    String::new(),
                ));
            }
            // Push extra_token at the bottom so DEDENTs come first
            // pending_tokens is a stack (pop from end), so we insert at 0
            self.pending_tokens.insert(0, extra_token);
            self.pending_tokens.pop()
        } else {
            // Same indent level - just return the extra token directly
            Some(extra_token)
        }
    }

    pub(super) fn handle_indentation(&mut self) -> Option<Token> {
        let start_pos = self.current_pos;
        let start_line = self.line;

        // Count leading spaces/tabs
        let mut indent = 0;
        while let Some(ch) = self.peek() {
            match ch {
                ' ' => {
                    indent += 1;
                    self.advance();
                }
                '\t' => {
                    indent += 4; // Tab = 4 spaces
                    self.advance();
                }
                '\n' => {
                    // Empty line, skip
                    self.advance();
                    self.line += 1;
                    self.column = 1;
                    indent = 0;
                }
                '#' => {
                    // Check if this is an attribute: #[
                    let hash_start = self.current_pos;
                    self.advance(); // Consume the '#'
                    let next = self.peek();
                    if next == Some('[') {
                        // This is an attribute, not a comment
                        let token = Token::new(
                            TokenKind::Hash,
                            Span::new(
                                self.current_pos - 1,
                                self.current_pos,
                                self.line,
                                self.column - 1,
                            ),
                            "#".to_string(),
                        );
                        return self.emit_with_indentation(indent, start_pos, start_line, token);
                    }
                    if next == Some('#') {
                        // Doc comment ## - emit DocComment token
                        self.advance(); // Consume second '#'
                        // Skip leading whitespace
                        while let Some(c) = self.peek() {
                            if c == ' ' || c == '\t' {
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        // Read content until newline
                        let mut content = String::new();
                        while let Some(c) = self.peek() {
                            if c == '\n' {
                                break;
                            }
                            content.push(c);
                            self.advance();
                        }
                        let token = Token::new(
                            TokenKind::DocComment(content.trim().to_string()),
                            Span::new(hash_start, self.current_pos, self.line, self.column),
                            self.source[hash_start..self.current_pos].to_string(),
                        );
                        return self.emit_with_indentation(indent, start_pos, start_line, token);
                    }
                    // Regular comment line, skip to end
                    while let Some(c) = self.peek() {
                        if c == '\n' {
                            break;
                        }
                        self.advance();
                    }
                    if self.peek() == Some('\n') {
                        self.advance();
                        self.line += 1;
                        self.column = 1;
                    }
                    indent = 0;
                }
                '/' => {
                    // Check if this is a block comment: /* or //
                    let slash_start = self.current_pos;
                    let slash_start_line = self.line;
                    let slash_start_col = self.column;
                    self.advance(); // Consume the '/'
                    if self.peek() == Some('*') {
                        self.advance(); // Consume the '*'
                        // Check for doc comment /** (but not /**/)
                        if self.peek() == Some('*') && self.peek_ahead(1) != Some('/') {
                            // Doc comment /** ... */
                            self.advance(); // Consume second '*'
                            let content = self.parse_nested_comment();
                            // Clean up the content
                            let cleaned = clean_doc_comment(&content);
                            let token = Token::new(
                                TokenKind::DocComment(cleaned),
                                Span::new(
                                    slash_start,
                                    self.current_pos,
                                    slash_start_line,
                                    slash_start_col,
                                ),
                                self.source[slash_start..self.current_pos].to_string(),
                            );
                            return self.emit_with_indentation(indent, start_pos, start_line, token);
                        }
                        // Regular block comment /* ... */
                        let mut depth = 1;
                        while depth > 0 {
                            match self.advance() {
                                Some((_, '*')) => {
                                    if self.peek() == Some('/') {
                                        self.advance();
                                        depth -= 1;
                                    }
                                }
                                Some((_, '/')) => {
                                    if self.peek() == Some('*') {
                                        self.advance();
                                        depth += 1;
                                    }
                                }
                                Some((_, '\n')) => {
                                    self.line += 1;
                                    self.column = 1;
                                }
                                Some(_) => {}
                                None => break,
                            }
                        }
                        indent = 0;
                    } else if self.peek() == Some('/') {
                        // Could be // (floor div) or /// (doc comment)
                        self.advance(); // Consume second '/'
                        if self.peek() == Some('/') {
                            // Doc comment /// ...
                            self.advance(); // Consume third '/'
                            // Check if this is a multi-line /// block (/// on its own line)
                            let is_block = {
                                let remaining = &self.source[self.current_pos..];
                                let line_rest = remaining.split('\n').next().unwrap_or("");
                                line_rest.trim().is_empty()
                            };
                            if is_block {
                                // Multi-line /// ... /// doc comment block
                                // Skip to end of current line (past the newline)
                                while let Some(ch) = self.peek() {
                                    if ch == '\n' {
                                        self.line += 1;
                                        self.column = 1;
                                        self.advance();
                                        break;
                                    }
                                    self.advance();
                                }
                                // Read content until we find a line that is just `///`
                                let mut content = String::new();
                                loop {
                                    let remaining = &self.source[self.current_pos..];
                                    let current_line = remaining.split('\n').next().unwrap_or("");
                                    if current_line.trim() == "///" {
                                        // Found closing ///, skip past it
                                        for _ in 0..current_line.len() {
                                            self.advance();
                                        }
                                        // Skip the newline after closing ///
                                        if self.peek() == Some('\n') {
                                            self.line += 1;
                                            self.column = 1;
                                            self.advance();
                                        }
                                        break;
                                    }
                                    match self.peek() {
                                        Some('\n') => {
                                            content.push('\n');
                                            self.line += 1;
                                            self.column = 1;
                                            self.advance();
                                        }
                                        Some(ch) => {
                                            content.push(ch);
                                            self.advance();
                                        }
                                        None => break,
                                    }
                                }
                                let token = Token::new(
                                    TokenKind::DocComment(content.trim().to_string()),
                                    Span::new(
                                        slash_start,
                                        self.current_pos,
                                        slash_start_line,
                                        slash_start_col,
                                    ),
                                    self.source[slash_start..self.current_pos].to_string(),
                                );
                                return self.emit_with_indentation(indent, start_pos, start_line, token);
                            }
                            let doc_start_pos = self.current_pos;
                            let doc_start_line = self.line;
                            let doc_start_col = self.column;
                            // Skip leading whitespace
                            while self.peek() == Some(' ') || self.peek() == Some('\t') {
                                self.advance();
                            }
                            // Read to end of line
                            let content_start = self.current_pos;
                            while let Some(c) = self.peek() {
                                if c == '\n' {
                                    break;
                                }
                                self.advance();
                            }
                            let content = self.source[content_start..self.current_pos].trim().to_string();
                            let token = Token::new(
                                TokenKind::DocComment(content),
                                Span::new(
                                    doc_start_pos - 3,
                                    self.current_pos,
                                    doc_start_line,
                                    doc_start_col - 3,
                                ),
                                self.source[doc_start_pos - 3..self.current_pos].to_string(),
                            );
                            return self.emit_with_indentation(indent, start_pos, start_line, token);
                        } else {
                            // Double slash // at line start: treat as a line comment
                            // (C-style comment syntax used in some Simple files).
                            // Floor division `//` would not appear at line start as a statement.
                            while let Some(c) = self.peek() {
                                if c == '\n' {
                                    break;
                                }
                                self.advance();
                            }
                            if self.peek() == Some('\n') {
                                self.advance();
                                self.line += 1;
                                self.column = 1;
                            }
                            indent = 0;
                        }
                    } else if self.peek() == Some('=') {
                        // Slash assign /=
                        self.advance(); // Consume '='
                        let token = Token::new(
                            TokenKind::SlashAssign,
                            Span::new(
                                self.current_pos - 2,
                                self.current_pos,
                                self.line,
                                self.column - 2,
                            ),
                            "/=".to_string(),
                        );
                        return self.emit_with_indentation(indent, start_pos, start_line, token);
                    } else {
                        // Not a block comment, it's a slash token
                        let token = Token::new(
                            TokenKind::Slash,
                            Span::new(
                                self.current_pos - 1,
                                self.current_pos,
                                self.line,
                                self.column - 1,
                            ),
                            "/".to_string(),
                        );
                        return self.emit_with_indentation(indent, start_pos, start_line, token);
                    }
                }
                _ => break,
            }
        }

        let current_indent = *self.indent_stack.last().unwrap_or(&0);

        if indent > current_indent {
            self.indent_stack.push(indent);
            Some(Token::new(
                TokenKind::Indent,
                Span::new(start_pos, self.current_pos, start_line, 1),
                String::new(),
            ))
        } else if indent < current_indent {
            // Generate DEDENT tokens
            while let Some(&top) = self.indent_stack.last() {
                if top <= indent {
                    break;
                }
                self.indent_stack.pop();
                self.pending_tokens.push(Token::new(
                    TokenKind::Dedent,
                    Span::new(start_pos, self.current_pos, start_line, 1),
                    String::new(),
                ));
            }
            self.pending_tokens.pop()
        } else {
            None
        }
    }
}
