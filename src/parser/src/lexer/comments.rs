use crate::token::{Span, Token, TokenKind};

impl<'a> super::Lexer<'a> {
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

    pub(super) fn read_doc_block_comment(
        &mut self,
        start_pos: usize,
        start_line: usize,
        start_column: usize,
    ) -> Token {
        // Read doc comment content until */ is found
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
                None => {
                    // Unterminated doc comment
                    break;
                }
            }
        }
        // Trim leading/trailing whitespace from each line and remove leading *
        let cleaned = content
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
            .to_string();

        Token::new(
            TokenKind::DocComment(cleaned),
            Span::new(start_pos, self.current_pos, start_line, start_column),
            self.source[start_pos..self.current_pos].to_string(),
        )
    }

    pub(super) fn read_doc_line_comment(
        &mut self,
        start_pos: usize,
        start_line: usize,
        start_column: usize,
    ) -> Token {
        // Read doc comment content until end of line
        let mut content = String::new();
        // Skip leading whitespace after ##
        while let Some(ch) = self.peek() {
            if ch == ' ' || ch == '\t' {
                self.advance();
            } else {
                break;
            }
        }
        // Read until newline
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
}
