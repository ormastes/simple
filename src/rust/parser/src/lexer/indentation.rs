use crate::token::{Span, Token, TokenKind};

use super::comments::clean_doc_comment;

impl<'a> super::Lexer<'a> {
    pub(super) fn handle_indentation(&mut self) -> Option<Token> {
        let start_pos = self.current_pos;
        let start_line = self.line;

        // Count leading spaces/tabs
        let mut indent = 0;
        let mut pending_token: Option<Token> = None;
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
                        pending_token = Some(Token::new(
                            TokenKind::Hash,
                            Span::new(self.current_pos - 1, self.current_pos, self.line, self.column - 1),
                            "#".to_string(),
                        ));
                        break;
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
                        pending_token = Some(Token::new(
                            TokenKind::DocComment(content.trim().to_string()),
                            Span::new(hash_start, self.current_pos, self.line, self.column),
                            self.source[hash_start..self.current_pos].to_string(),
                        ));
                        break;
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
                            return Some(Token::new(
                                TokenKind::DocComment(cleaned),
                                Span::new(slash_start, self.current_pos, slash_start_line, slash_start_col),
                                self.source[slash_start..self.current_pos].to_string(),
                            ));
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
                            let start_pos = slash_start;
                            let start_line = slash_start_line;
                            let start_col = slash_start_col;
                            // Skip leading whitespace
                            while self.peek() == Some(' ') || self.peek() == Some('\t') {
                                self.advance();
                            }

                            // Check if this is a multi-line doc block (/// on its own line)
                            if self.peek() == Some('\n') || self.peek().is_none() {
                                // Multi-line doc block: ///\n...\n///
                                return Some(self.read_doc_block_triple_slash(start_pos, start_line, start_col));
                            }

                            // Read to end of line (single-line doc comment)
                            let content_start = self.current_pos;
                            while let Some(c) = self.peek() {
                                if c == '\n' {
                                    break;
                                }
                                self.advance();
                            }
                            let content = self.source[content_start..self.current_pos].trim().to_string();
                            return Some(Token::new(
                                TokenKind::DocComment(content),
                                Span::new(start_pos, self.current_pos, start_line, start_col),
                                self.source[start_pos..self.current_pos].to_string(),
                            ));
                        } else {
                            // Double slash // - return DoubleSlash token
                            return Some(Token::new(
                                TokenKind::DoubleSlash,
                                Span::new(self.current_pos - 2, self.current_pos, self.line, self.column - 2),
                                "//".to_string(),
                            ));
                        }
                    } else if self.peek() == Some('=') {
                        // Slash assign /=
                        self.advance(); // Consume '='
                        return Some(Token::new(
                            TokenKind::SlashAssign,
                            Span::new(self.current_pos - 2, self.current_pos, self.line, self.column - 2),
                            "/=".to_string(),
                        ));
                    } else {
                        // Not a block comment, it's a slash token
                        return Some(Token::new(
                            TokenKind::Slash,
                            Span::new(self.current_pos - 1, self.current_pos, self.line, self.column - 1),
                            "/".to_string(),
                        ));
                    }
                }
                _ => break,
            }
        }

        if let Some(token) = pending_token {
            let current_indent = *self.indent_stack.last().unwrap_or(&0);
            if indent > current_indent {
                self.indent_stack.push(indent);
                self.pending_tokens.push(token);
                return Some(Token::new(
                    TokenKind::Indent,
                    Span::new(start_pos, self.current_pos, start_line, 1),
                    String::new(),
                ));
            } else if indent < current_indent {
                self.pending_tokens.push(token);
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
                return self.pending_tokens.pop();
            }
            return Some(token);
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
