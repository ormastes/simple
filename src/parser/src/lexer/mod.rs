mod comments;
mod escapes;
mod identifiers;
mod indentation;
mod numbers;
mod strings;

pub use crate::token::NumericSuffix;
use crate::token::{Span, Token, TokenKind};

pub struct Lexer<'a> {
    source: &'a str,
    chars: std::iter::Peekable<std::str::CharIndices<'a>>,
    current_pos: usize,
    line: usize,
    column: usize,
    indent_stack: Vec<usize>,
    pending_tokens: Vec<Token>,
    at_line_start: bool,
    /// Track bracket depth to suppress INDENT/DEDENT inside delimiters
    bracket_depth: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: source.char_indices().peekable(),
            current_pos: 0,
            line: 1,
            column: 1,
            indent_stack: vec![0],
            pending_tokens: Vec::new(),
            at_line_start: true,
            bracket_depth: 0,
        }
    }

    pub fn tokenize(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();

        loop {
            let token = self.next_token();
            let is_eof = token.kind == TokenKind::Eof;
            tokens.push(token);
            if is_eof {
                break;
            }
        }

        tokens
    }

    pub fn next_token(&mut self) -> Token {
        // Return pending tokens first (for INDENT/DEDENT)
        if let Some(token) = self.pending_tokens.pop() {
            return token;
        }

        // Handle indentation at line start (but not inside brackets)
        if self.at_line_start {
            self.at_line_start = false;
            // Skip indentation handling when inside brackets/parens/braces
            if self.bracket_depth == 0 {
                if let Some(indent_token) = self.handle_indentation() {
                    return indent_token;
                }
            } else {
                // Still need to skip whitespace at line start when inside brackets
                while let Some(ch) = self.peek() {
                    match ch {
                        ' ' | '\t' => {
                            self.advance();
                        }
                        '\n' => {
                            // Empty line inside brackets
                            self.advance();
                            self.line += 1;
                            self.column = 1;
                        }
                        _ => break,
                    }
                }
            }
        }

        self.skip_whitespace();

        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        let Some((_pos, ch)) = self.advance() else {
            // Generate remaining DEDENTs at EOF
            while self.indent_stack.len() > 1 {
                self.indent_stack.pop();
                self.pending_tokens.push(Token::new(
                    TokenKind::Dedent,
                    Span::new(start_pos, start_pos, start_line, start_column),
                    String::new(),
                ));
            }
            if let Some(token) = self.pending_tokens.pop() {
                return token;
            }
            return Token::new(
                TokenKind::Eof,
                Span::new(start_pos, start_pos, start_line, start_column),
                String::new(),
            );
        };

        let kind = match ch {
            // Newline
            '\n' => {
                self.line += 1;
                self.column = 1;
                self.at_line_start = true;
                TokenKind::Newline
            }

            // Single-character tokens - track bracket depth for indentation suppression
            '(' => {
                self.bracket_depth += 1;
                TokenKind::LParen
            }
            ')' => {
                self.bracket_depth = self.bracket_depth.saturating_sub(1);
                TokenKind::RParen
            }
            '[' => {
                self.bracket_depth += 1;
                TokenKind::LBracket
            }
            ']' => {
                self.bracket_depth = self.bracket_depth.saturating_sub(1);
                TokenKind::RBracket
            }
            '{' => {
                self.bracket_depth += 1;
                TokenKind::LBrace
            }
            '}' => {
                self.bracket_depth = self.bracket_depth.saturating_sub(1);
                TokenKind::RBrace
            }
            ',' => TokenKind::Comma,
            ';' => TokenKind::Semicolon,
            '@' => TokenKind::At,
            '#' => {
                // Check if this is an attribute: #[
                if self.peek() == Some('[') {
                    TokenKind::Hash
                } else if self.peek() == Some('#') {
                    // Doc comment: ## ...
                    self.advance(); // consume second '#'
                    return self.read_doc_line_comment(start_pos, start_line, start_column);
                } else {
                    // Otherwise it's a regular comment
                    self.skip_comment()
                }
            }
            '$' => TokenKind::Dollar,
            '\\' => {
                // Line continuation: backslash followed by newline
                if self.peek() == Some('\n') {
                    self.advance(); // consume the newline
                    self.line += 1;
                    self.column = 1;
                    // Return next meaningful token instead of backslash
                    return self.next_token();
                }
                TokenKind::Backslash
            }
            '^' => TokenKind::Caret,
            '~' => TokenKind::Tilde,
            '?' => TokenKind::Question,

            // Multi-character operators
            '+' => self.match_char('=', TokenKind::PlusAssign, TokenKind::Plus),
            '-' => {
                if self.check('>') {
                    self.advance();
                    TokenKind::Arrow
                } else if self.check('=') {
                    self.advance();
                    TokenKind::MinusAssign
                } else {
                    TokenKind::Minus
                }
            }
            '*' => {
                if self.check('*') {
                    self.advance();
                    TokenKind::DoubleStar
                } else if self.check('=') {
                    self.advance();
                    TokenKind::StarAssign
                } else {
                    TokenKind::Star
                }
            }
            '/' => {
                if self.check('*') {
                    self.advance(); // consume '*'
                    if self.peek() == Some('*') && self.peek_ahead(1) != Some('/') {
                        // Doc comment /** ... */
                        self.advance(); // consume second '*'
                        return self.read_doc_block_comment(start_pos, start_line, start_column);
                    } else {
                        // Regular block comment /* ... */
                        self.skip_block_comment()
                    }
                } else if self.check('/') {
                    self.advance(); // consume second '/'
                    if self.check('/') {
                        // Doc comment /// ...
                        self.advance(); // consume third '/'
                        return self.read_doc_line_comment(start_pos, start_line, start_column);
                    } else {
                        // Floor division //
                        TokenKind::DoubleSlash
                    }
                } else if self.check('=') {
                    self.advance();
                    TokenKind::SlashAssign
                } else {
                    TokenKind::Slash
                }
            }
            '%' => TokenKind::Percent,
            '&' => TokenKind::Ampersand,
            '|' => TokenKind::Pipe,

            '=' => {
                if self.check('=') {
                    self.advance();
                    TokenKind::Eq
                } else if self.check('>') {
                    self.advance();
                    TokenKind::FatArrow
                } else {
                    TokenKind::Assign
                }
            }
            '!' => {
                if self.check('=') {
                    self.advance();
                    TokenKind::NotEq
                } else {
                    // Standalone ! for macro invocations
                    TokenKind::Bang
                }
            }
            '<' => {
                if self.check('=') {
                    self.advance();
                    TokenKind::LtEq
                } else if self.check('<') {
                    self.advance();
                    TokenKind::ShiftLeft
                } else {
                    TokenKind::Lt
                }
            }
            '>' => {
                if self.check('=') {
                    self.advance();
                    TokenKind::GtEq
                } else if self.check('>') {
                    self.advance();
                    TokenKind::ShiftRight
                } else {
                    TokenKind::Gt
                }
            }
            ':' => {
                if self.check(':') {
                    self.advance();
                    TokenKind::DoubleColon
                } else if self.check_alpha() {
                    // Symbol literal :name
                    self.scan_symbol()
                } else {
                    TokenKind::Colon
                }
            }
            '.' => {
                if self.check('.') {
                    self.advance();
                    if self.check('.') {
                        self.advance();
                        TokenKind::Ellipsis
                    } else if self.check('=') {
                        self.advance();
                        TokenKind::DoubleDotEq
                    } else {
                        TokenKind::DoubleDot
                    }
                } else {
                    TokenKind::Dot
                }
            }

            // String literals
            '"' => {
                // Check for triple-quoted string (docstring)
                if self.check('"') && self.check_ahead(1, '"') {
                    self.scan_triple_quoted_string()
                } else {
                    self.scan_fstring() // Double quotes are interpolated by default
                }
            }
            '\'' => self.scan_raw_string(), // Single quotes are raw strings

            // Numbers
            '0'..='9' => self.scan_number(ch),

            // Identifiers and keywords
            'a'..='z' | 'A'..='Z' | '_' => self.scan_identifier(ch),

            _ => TokenKind::Error(format!("Unexpected character: '{}'", ch)),
        };

        let end_pos = self.current_pos;
        let lexeme = self.source[start_pos..end_pos].to_string();

        Token::new(
            kind,
            Span::new(start_pos, end_pos, start_line, start_column),
            lexeme,
        )
    }

    fn advance(&mut self) -> Option<(usize, char)> {
        if let Some((pos, ch)) = self.chars.next() {
            self.current_pos = pos + ch.len_utf8();
            self.column += 1;
            Some((pos, ch))
        } else {
            None
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, ch)| *ch)
    }

    fn peek_ahead(&self, n: usize) -> Option<char> {
        self.source[self.current_pos..].chars().nth(n)
    }

    fn check(&mut self, expected: char) -> bool {
        self.peek() == Some(expected)
    }

    fn check_ahead(&mut self, n: usize, expected: char) -> bool {
        self.peek_ahead(n) == Some(expected)
    }

    fn check_alpha(&mut self) -> bool {
        self.peek()
            .map(|c| c.is_alphabetic() || c == '_')
            .unwrap_or(false)
    }

    fn match_char(
        &mut self,
        expected: char,
        if_match: TokenKind,
        otherwise: TokenKind,
    ) -> TokenKind {
        if self.check(expected) {
            self.advance();
            if_match
        } else {
            otherwise
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch == ' ' || ch == '\t' || ch == '\r' {
                self.advance();
            } else {
                break;
            }
        }
    }
}

#[cfg(test)]
#[path = "../lexer_tests.rs"]
mod tests;
