//! SDN lexer - tokenizes SDN input with INDENT/DEDENT handling.

use crate::error::{Result, Span};

/// SDN token kinds.
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    Integer(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Null,

    // Identifiers
    Identifier(String),

    // Keywords
    Table, // table

    // Operators and punctuation
    Colon,    // :
    Equals,   // =
    Pipe,     // |
    Comma,    // ,
    LBrace,   // {
    RBrace,   // }
    LBracket, // [
    RBracket, // ]
    LParen,   // (
    RParen,   // )

    // Whitespace-significant
    Newline,
    Indent,
    Dedent,

    // End of file
    Eof,
}

impl TokenKind {
    pub fn name(&self) -> &'static str {
        match self {
            TokenKind::Integer(_) => "integer",
            TokenKind::Float(_) => "float",
            TokenKind::String(_) => "string",
            TokenKind::Bool(_) => "bool",
            TokenKind::Null => "null",
            TokenKind::Identifier(_) => "identifier",
            TokenKind::Table => "table",
            TokenKind::Colon => ":",
            TokenKind::Equals => "=",
            TokenKind::Pipe => "|",
            TokenKind::Comma => ",",
            TokenKind::LBrace => "{",
            TokenKind::RBrace => "}",
            TokenKind::LBracket => "[",
            TokenKind::RBracket => "]",
            TokenKind::LParen => "(",
            TokenKind::RParen => ")",
            TokenKind::Newline => "newline",
            TokenKind::Indent => "INDENT",
            TokenKind::Dedent => "DEDENT",
            TokenKind::Eof => "EOF",
        }
    }
}

/// SDN token with kind and source location.
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub lexeme: String,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span, lexeme: String) -> Self {
        Self { kind, span, lexeme }
    }
}

/// SDN lexer with indentation tracking.
pub struct Lexer<'a> {
    source: &'a str,
    chars: std::iter::Peekable<std::str::CharIndices<'a>>,
    current_pos: usize,
    line: usize,
    column: usize,
    indent_stack: Vec<usize>,
    pending_tokens: Vec<Token>,
    at_line_start: bool,
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

    /// Tokenize the entire source into a vector of tokens.
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

    /// Get the next token.
    pub fn next_token(&mut self) -> Token {
        // Return pending tokens first (for INDENT/DEDENT)
        if let Some(token) = self.pending_tokens.pop() {
            return token;
        }

        // Handle indentation at line start (but not inside brackets)
        if self.at_line_start {
            self.at_line_start = false;
            if self.bracket_depth == 0 {
                if let Some(indent_token) = self.handle_indentation() {
                    return indent_token;
                }
            } else {
                // Skip whitespace at line start when inside brackets
                while let Some(ch) = self.peek() {
                    match ch {
                        ' ' | '\t' => {
                            self.advance();
                        }
                        '\n' => {
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
            '\n' => {
                self.line += 1;
                self.column = 1;
                self.at_line_start = true;
                TokenKind::Newline
            }

            // Single-character tokens with bracket depth tracking
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
            ':' => TokenKind::Colon,
            '=' => TokenKind::Equals,
            '|' => TokenKind::Pipe,

            // Comments
            '#' => {
                self.skip_comment();
                return self.next_token();
            }

            // Strings
            '"' => self.scan_string('"'),

            // Numbers or negative numbers
            '-' if self.peek().is_some_and(|c| c.is_ascii_digit()) => self.scan_number(ch),

            // Numbers
            c if c.is_ascii_digit() => self.scan_number(c),

            // Identifiers and keywords
            c if c.is_alphabetic() || c == '_' => self.scan_identifier(c),

            _ => {
                // Unknown character - skip and try again
                return self.next_token();
            }
        };

        let end_pos = self.current_pos;
        let lexeme = self.source[start_pos..end_pos].to_string();
        Token::new(kind, Span::new(start_pos, end_pos, start_line, start_column), lexeme)
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, c)| *c)
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

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch == ' ' || ch == '\t' {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn skip_comment(&mut self) {
        while let Some(ch) = self.peek() {
            if ch == '\n' {
                break;
            }
            self.advance();
        }
    }

    fn handle_indentation(&mut self) -> Option<Token> {
        let start_pos = self.current_pos;
        let start_line = self.line;

        // Count spaces at start of line
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
                    // Empty line - skip and check again
                    self.advance();
                    self.line += 1;
                    self.column = 1;
                    indent = 0;
                }
                '#' => {
                    // Comment line - skip entire line
                    self.skip_comment();
                    if let Some('\n') = self.peek() {
                        self.advance();
                        self.line += 1;
                        self.column = 1;
                        indent = 0;
                    } else {
                        // EOF after comment
                        break;
                    }
                }
                _ => break,
            }
        }

        let current_indent = *self.indent_stack.last().unwrap();

        if indent > current_indent {
            // INDENT
            self.indent_stack.push(indent);
            Some(Token::new(
                TokenKind::Indent,
                Span::new(start_pos, self.current_pos, start_line, 1),
                String::new(),
            ))
        } else if indent < current_indent {
            // DEDENT(s) - may need multiple
            while let Some(&top) = self.indent_stack.last() {
                if top > indent {
                    self.indent_stack.pop();
                    self.pending_tokens.push(Token::new(
                        TokenKind::Dedent,
                        Span::new(start_pos, self.current_pos, start_line, 1),
                        String::new(),
                    ));
                } else {
                    break;
                }
            }
            self.pending_tokens.pop()
        } else {
            None
        }
    }

    fn scan_string(&mut self, _quote: char) -> TokenKind {
        let mut value = String::new();

        loop {
            match self.peek() {
                Some('"') => {
                    self.advance();
                    break;
                }
                Some('\\') => {
                    self.advance();
                    if let Some(escaped) = self.peek() {
                        self.advance();
                        match escaped {
                            'n' => value.push('\n'),
                            't' => value.push('\t'),
                            'r' => value.push('\r'),
                            '\\' => value.push('\\'),
                            '"' => value.push('"'),
                            _ => {
                                value.push('\\');
                                value.push(escaped);
                            }
                        }
                    }
                }
                Some(ch) => {
                    self.advance();
                    value.push(ch);
                }
                None => break, // Unclosed string - will be caught by parser
            }
        }

        TokenKind::String(value)
    }

    fn scan_number(&mut self, first: char) -> TokenKind {
        let mut value = String::new();
        value.push(first);

        let mut has_dot = false;
        let mut has_exp = false;

        while let Some(ch) = self.peek() {
            match ch {
                '0'..='9' => {
                    self.advance();
                    value.push(ch);
                }
                '_' => {
                    // Underscore separator in numbers
                    self.advance();
                }
                '.' if !has_dot && !has_exp => {
                    // Check if next char is a digit
                    let mut chars_clone = self.source[self.current_pos..].chars();
                    let next_next = chars_clone.nth(1);
                    if next_next.is_some_and(|c| c.is_ascii_digit()) {
                        self.advance();
                        value.push('.');
                        has_dot = true;
                    } else {
                        break;
                    }
                }
                'e' | 'E' if !has_exp => {
                    self.advance();
                    value.push(ch);
                    has_exp = true;
                    // Handle optional sign after exponent
                    if let Some(sign) = self.peek() {
                        if sign == '+' || sign == '-' {
                            self.advance();
                            value.push(sign);
                        }
                    }
                }
                _ => break,
            }
        }

        if has_dot || has_exp {
            match value.parse::<f64>() {
                Ok(f) => TokenKind::Float(f),
                Err(_) => TokenKind::Float(0.0),
            }
        } else {
            match value.parse::<i64>() {
                Ok(i) => TokenKind::Integer(i),
                Err(_) => TokenKind::Integer(0),
            }
        }
    }

    fn scan_identifier(&mut self, first: char) -> TokenKind {
        let mut value = String::new();
        value.push(first);

        while let Some(ch) = self.peek() {
            // Allow common path/URL characters in bare identifiers
            // This includes # for URL anchors (e.g., file.md#section)
            if ch.is_alphanumeric() || ch == '_' || ch == '/' || ch == '.' || ch == '-' || ch == '#' {
                self.advance();
                value.push(ch);
            } else {
                break;
            }
        }

        // Check for keywords
        match value.as_str() {
            "true" => TokenKind::Bool(true),
            "false" => TokenKind::Bool(false),
            "null" | "nil" => TokenKind::Null,
            "table" => TokenKind::Table,
            _ => TokenKind::Identifier(value),
        }
    }
}

/// Parse result from lexer.
pub fn tokenize(source: &str) -> Result<Vec<Token>> {
    let mut lexer = Lexer::new(source);
    Ok(lexer.tokenize())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(src: &str) -> Vec<TokenKind> {
        let mut lexer = Lexer::new(src);
        lexer
            .tokenize()
            .into_iter()
            .map(|t| t.kind)
            .filter(|k| !matches!(k, TokenKind::Newline))
            .collect()
    }

    #[test]
    fn test_simple_values() {
        assert_eq!(
            lex("name: Alice"),
            vec![
                TokenKind::Identifier("name".into()),
                TokenKind::Colon,
                TokenKind::Identifier("Alice".into()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_numbers() {
        assert_eq!(lex("42"), vec![TokenKind::Integer(42), TokenKind::Eof]);
        assert_eq!(lex("-17"), vec![TokenKind::Integer(-17), TokenKind::Eof]);
        assert_eq!(lex("3.15"), vec![TokenKind::Float(3.15), TokenKind::Eof]);
        assert_eq!(lex("1_000_000"), vec![TokenKind::Integer(1000000), TokenKind::Eof]);
    }

    #[test]
    fn test_strings() {
        assert_eq!(
            lex(r#""Hello, World!""#),
            vec![TokenKind::String("Hello, World!".into()), TokenKind::Eof]
        );
    }

    #[test]
    fn test_booleans() {
        assert_eq!(lex("true"), vec![TokenKind::Bool(true), TokenKind::Eof]);
        assert_eq!(lex("false"), vec![TokenKind::Bool(false), TokenKind::Eof]);
    }

    #[test]
    fn test_null() {
        assert_eq!(lex("null"), vec![TokenKind::Null, TokenKind::Eof]);
        assert_eq!(lex("nil"), vec![TokenKind::Null, TokenKind::Eof]);
    }

    #[test]
    fn test_inline_dict() {
        let tokens = lex("{x: 10, y: 20}");
        assert!(tokens.contains(&TokenKind::LBrace));
        assert!(tokens.contains(&TokenKind::RBrace));
        assert!(tokens.contains(&TokenKind::Comma));
    }

    #[test]
    fn test_inline_array() {
        let tokens = lex("[1, 2, 3]");
        assert!(tokens.contains(&TokenKind::LBracket));
        assert!(tokens.contains(&TokenKind::RBracket));
    }

    #[test]
    fn test_table_syntax() {
        let tokens = lex("|id, name|");
        assert!(tokens.contains(&TokenKind::Pipe));
    }

    #[test]
    fn test_indentation() {
        let src = "server:\n    host: localhost";
        let mut lexer = Lexer::new(src);
        let tokens: Vec<_> = lexer.tokenize().into_iter().map(|t| t.kind).collect();
        assert!(tokens.contains(&TokenKind::Indent));
    }

    #[test]
    fn test_comments() {
        let tokens = lex("# comment\nname: Alice");
        assert_eq!(tokens[0], TokenKind::Identifier("name".into()));
    }
}
