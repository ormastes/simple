//! SUI Template Lexer
//!
//! Lexes `.sui` template files with HTML content and template blocks.
//!
//! # Template Syntax
//!
//! | Syntax | Name | Purpose |
//! |--------|------|---------|
//! | `{@ ... @}` | Directive | Component/page declaration |
//! | `{$ ... $}` | Declaration | State fields |
//! | `{- ... -}` | Server block | Server-side code |
//! | `{+ ... +}` | Client block | Client-side code |
//! | `{{ expr }}` | Output | HTML-escaped expression |
//! | `{! expr !}` | Raw output | Unescaped output |
//! | `{% ... %}` | Control | if/for/let statements |
//! | `{# ... #}` | Comment | Ignored |

mod tokens;

pub use tokens::{Span, SuiToken, SuiTokenKind};

/// Lexer mode for context-sensitive tokenization
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LexerMode {
    /// Outside any template block - scanning HTML/text
    Html,
    /// Inside a directive block `{@ @}`
    Directive,
    /// Inside a declaration block `{$ $}`
    Declaration,
    /// Inside a server block `{- -}`
    Server,
    /// Inside a client block `{+ +}`
    Client,
    /// Inside an output block `{{ }}`
    Output,
    /// Inside a raw output block `{! !}`
    RawOutput,
    /// Inside a control block `{% %}`
    Control,
    /// Inside a comment block `{# #}`
    Comment,
    /// Inside an HTML tag `< >`
    Tag,
}

/// SUI template lexer
pub struct SuiLexer<'a> {
    source: &'a str,
    chars: std::iter::Peekable<std::str::CharIndices<'a>>,
    current_pos: usize,
    line: usize,
    column: usize,
    mode: LexerMode,
    mode_stack: Vec<LexerMode>,
}

impl<'a> SuiLexer<'a> {
    /// Create a new lexer for the given source
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: source.char_indices().peekable(),
            current_pos: 0,
            line: 1,
            column: 1,
            mode: LexerMode::Html,
            mode_stack: Vec::new(),
        }
    }

    /// Tokenize the entire source into a vector of tokens
    pub fn tokenize(&mut self) -> Vec<SuiToken> {
        let mut tokens = Vec::new();
        loop {
            let token = self.next_token();
            let is_eof = token.kind == SuiTokenKind::Eof;
            tokens.push(token);
            if is_eof {
                break;
            }
        }
        tokens
    }

    /// Get the next token
    pub fn next_token(&mut self) -> SuiToken {
        match self.mode {
            LexerMode::Html => self.scan_html(),
            LexerMode::Tag => self.scan_tag(),
            LexerMode::Comment => self.scan_comment(),
            _ => self.scan_code(),
        }
    }

    /// Scan HTML content (outside template blocks)
    fn scan_html(&mut self) -> SuiToken {
        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        // Check for EOF
        let Some(ch) = self.peek() else {
            return self.make_token(SuiTokenKind::Eof, start_pos, start_line, start_column);
        };

        // Check for template block openers
        if ch == '{' {
            if let Some(token) = self.try_scan_block_open() {
                return token;
            }
        }

        // Check for HTML tag
        if ch == '<' {
            return self.scan_html_tag_start();
        }

        // Scan text content until we hit a block opener or tag
        self.scan_text()
    }

    /// Try to scan a template block opener
    fn try_scan_block_open(&mut self) -> Option<SuiToken> {
        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        // Peek at the next two characters
        let first = self.peek()?;
        let second = self.peek_ahead(1)?;

        if first != '{' {
            return None;
        }

        let (kind, new_mode) = match second {
            '@' => (SuiTokenKind::DirectiveOpen, LexerMode::Directive),
            '$' => (SuiTokenKind::DeclOpen, LexerMode::Declaration),
            '-' => (SuiTokenKind::ServerOpen, LexerMode::Server),
            '+' => (SuiTokenKind::ClientOpen, LexerMode::Client),
            '{' => (SuiTokenKind::OutputOpen, LexerMode::Output),
            '!' => (SuiTokenKind::RawOutputOpen, LexerMode::RawOutput),
            '%' => (SuiTokenKind::ControlOpen, LexerMode::Control),
            '#' => (SuiTokenKind::CommentOpen, LexerMode::Comment),
            _ => return None,
        };

        // Consume the two characters
        self.advance();
        self.advance();

        // Push current mode and switch
        self.mode_stack.push(self.mode);
        self.mode = new_mode;

        Some(self.make_token(kind, start_pos, start_line, start_column))
    }

    /// Scan text content
    fn scan_text(&mut self) -> SuiToken {
        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        let mut text = String::new();

        while let Some(ch) = self.peek() {
            // Stop at template block openers
            if ch == '{' {
                if let Some(next) = self.peek_ahead(1) {
                    if matches!(next, '@' | '$' | '-' | '+' | '{' | '!' | '%' | '#') {
                        break;
                    }
                }
            }
            // Stop at HTML tags
            if ch == '<' {
                break;
            }

            text.push(ch);
            self.advance();
        }

        if text.is_empty() {
            // Shouldn't happen, but handle gracefully
            return self.next_token();
        }

        SuiToken::new(
            SuiTokenKind::Text(text.clone()),
            Span::new(start_pos, self.current_pos, start_line, start_column),
            text,
        )
    }

    /// Scan HTML tag start
    fn scan_html_tag_start(&mut self) -> SuiToken {
        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        self.advance(); // consume '<'

        // Check for closing tag
        if self.peek() == Some('/') {
            self.advance();
            self.mode_stack.push(self.mode);
            self.mode = LexerMode::Tag;
            return self.make_token(SuiTokenKind::TagEndOpen, start_pos, start_line, start_column);
        }

        self.mode_stack.push(self.mode);
        self.mode = LexerMode::Tag;
        self.make_token(SuiTokenKind::TagOpen, start_pos, start_line, start_column)
    }

    /// Scan inside an HTML tag
    fn scan_tag(&mut self) -> SuiToken {
        self.skip_whitespace();

        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        let Some(ch) = self.peek() else {
            return self.make_token(SuiTokenKind::Eof, start_pos, start_line, start_column);
        };

        match ch {
            '>' => {
                self.advance();
                self.mode = self.mode_stack.pop().unwrap_or(LexerMode::Html);
                self.make_token(SuiTokenKind::TagClose, start_pos, start_line, start_column)
            }
            '/' if self.peek_ahead(1) == Some('>') => {
                self.advance();
                self.advance();
                self.mode = self.mode_stack.pop().unwrap_or(LexerMode::Html);
                self.make_token(SuiTokenKind::TagSelfClose, start_pos, start_line, start_column)
            }
            '=' => {
                self.advance();
                self.make_token(SuiTokenKind::Assign, start_pos, start_line, start_column)
            }
            '"' | '\'' => self.scan_string(ch),
            '{' => {
                // Template expression in attribute
                if let Some(token) = self.try_scan_block_open() {
                    return token;
                }
                self.advance();
                self.make_token(SuiTokenKind::LBrace, start_pos, start_line, start_column)
            }
            _ if ch.is_alphabetic() || ch == '_' || ch == ':' || ch == '-' => {
                self.scan_identifier()
            }
            _ => {
                self.advance();
                self.make_token(
                    SuiTokenKind::Error(format!("Unexpected character in tag: '{}'", ch)),
                    start_pos,
                    start_line,
                    start_column,
                )
            }
        }
    }

    /// Scan code inside template blocks
    fn scan_code(&mut self) -> SuiToken {
        self.skip_whitespace();

        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        let Some(ch) = self.peek() else {
            return self.make_token(SuiTokenKind::Eof, start_pos, start_line, start_column);
        };

        // Check for block closers
        if let Some(token) = self.try_scan_block_close() {
            return token;
        }

        match ch {
            // String literals
            '"' | '\'' => self.scan_string(ch),

            // Numbers
            '0'..='9' => self.scan_number(),

            // Identifiers and keywords
            'a'..='z' | 'A'..='Z' | '_' => self.scan_identifier(),

            // Operators and punctuation
            '=' => {
                self.advance();
                if self.peek() == Some('=') {
                    self.advance();
                    self.make_token(SuiTokenKind::Eq, start_pos, start_line, start_column)
                } else if self.peek() == Some('>') {
                    self.advance();
                    self.make_token(SuiTokenKind::Arrow, start_pos, start_line, start_column)
                } else {
                    self.make_token(SuiTokenKind::Assign, start_pos, start_line, start_column)
                }
            }
            '!' => {
                self.advance();
                if self.peek() == Some('=') {
                    self.advance();
                    self.make_token(SuiTokenKind::NotEq, start_pos, start_line, start_column)
                } else {
                    self.make_token(SuiTokenKind::Not, start_pos, start_line, start_column)
                }
            }
            '<' => {
                self.advance();
                if self.peek() == Some('=') {
                    self.advance();
                    self.make_token(SuiTokenKind::LtEq, start_pos, start_line, start_column)
                } else {
                    self.make_token(SuiTokenKind::Lt, start_pos, start_line, start_column)
                }
            }
            '>' => {
                self.advance();
                if self.peek() == Some('=') {
                    self.advance();
                    self.make_token(SuiTokenKind::GtEq, start_pos, start_line, start_column)
                } else {
                    self.make_token(SuiTokenKind::Gt, start_pos, start_line, start_column)
                }
            }
            '+' => {
                self.advance();
                self.make_token(SuiTokenKind::Plus, start_pos, start_line, start_column)
            }
            '-' => {
                self.advance();
                self.make_token(SuiTokenKind::Minus, start_pos, start_line, start_column)
            }
            '*' => {
                self.advance();
                self.make_token(SuiTokenKind::Star, start_pos, start_line, start_column)
            }
            '/' => {
                self.advance();
                self.make_token(SuiTokenKind::Slash, start_pos, start_line, start_column)
            }
            '%' => {
                self.advance();
                self.make_token(SuiTokenKind::Percent, start_pos, start_line, start_column)
            }
            '.' => {
                self.advance();
                if self.peek() == Some('.') {
                    self.advance();
                    self.make_token(SuiTokenKind::DoubleDot, start_pos, start_line, start_column)
                } else {
                    self.make_token(SuiTokenKind::Dot, start_pos, start_line, start_column)
                }
            }
            ':' => {
                self.advance();
                self.make_token(SuiTokenKind::Colon, start_pos, start_line, start_column)
            }
            ',' => {
                self.advance();
                self.make_token(SuiTokenKind::Comma, start_pos, start_line, start_column)
            }
            ';' => {
                self.advance();
                self.make_token(SuiTokenKind::Semicolon, start_pos, start_line, start_column)
            }
            '(' => {
                self.advance();
                self.make_token(SuiTokenKind::LParen, start_pos, start_line, start_column)
            }
            ')' => {
                self.advance();
                self.make_token(SuiTokenKind::RParen, start_pos, start_line, start_column)
            }
            '[' => {
                self.advance();
                self.make_token(SuiTokenKind::LBracket, start_pos, start_line, start_column)
            }
            ']' => {
                self.advance();
                self.make_token(SuiTokenKind::RBracket, start_pos, start_line, start_column)
            }
            '{' => {
                self.advance();
                self.make_token(SuiTokenKind::LBrace, start_pos, start_line, start_column)
            }
            '}' => {
                self.advance();
                self.make_token(SuiTokenKind::RBrace, start_pos, start_line, start_column)
            }
            '|' => {
                self.advance();
                if self.peek() == Some('|') {
                    self.advance();
                    self.make_token(SuiTokenKind::Or, start_pos, start_line, start_column)
                } else {
                    self.make_token(SuiTokenKind::Pipe, start_pos, start_line, start_column)
                }
            }
            '&' if self.peek_ahead(1) == Some('&') => {
                self.advance();
                self.advance();
                self.make_token(SuiTokenKind::And, start_pos, start_line, start_column)
            }
            '\n' => {
                self.advance();
                self.make_token(SuiTokenKind::Newline, start_pos, start_line, start_column)
            }
            _ => {
                self.advance();
                self.make_token(
                    SuiTokenKind::Error(format!("Unexpected character: '{}'", ch)),
                    start_pos,
                    start_line,
                    start_column,
                )
            }
        }
    }

    /// Try to scan a block closer
    fn try_scan_block_close(&mut self) -> Option<SuiToken> {
        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        let first = self.peek()?;
        let second = self.peek_ahead(1)?;

        let kind = match (self.mode, first, second) {
            (LexerMode::Directive, '@', '}') => SuiTokenKind::DirectiveClose,
            (LexerMode::Declaration, '$', '}') => SuiTokenKind::DeclClose,
            (LexerMode::Server, '-', '}') => SuiTokenKind::ServerClose,
            (LexerMode::Client, '+', '}') => SuiTokenKind::ClientClose,
            (LexerMode::Output, '}', '}') => SuiTokenKind::OutputClose,
            (LexerMode::RawOutput, '!', '}') => SuiTokenKind::RawOutputClose,
            (LexerMode::Control, '%', '}') => SuiTokenKind::ControlClose,
            _ => return None,
        };

        self.advance();
        self.advance();
        self.mode = self.mode_stack.pop().unwrap_or(LexerMode::Html);

        Some(self.make_token(kind, start_pos, start_line, start_column))
    }

    /// Scan comment content
    fn scan_comment(&mut self) -> SuiToken {
        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        let mut content = String::new();

        while let Some(ch) = self.peek() {
            // Check for comment close
            if ch == '#' && self.peek_ahead(1) == Some('}') {
                break;
            }
            content.push(ch);
            if ch == '\n' {
                self.line += 1;
                self.column = 0;
            }
            self.advance();
        }

        // Consume the closing #}
        if self.peek() == Some('#') && self.peek_ahead(1) == Some('}') {
            self.advance();
            self.advance();
            self.mode = self.mode_stack.pop().unwrap_or(LexerMode::Html);
        }

        SuiToken::new(
            SuiTokenKind::Comment(content.clone()),
            Span::new(start_pos, self.current_pos, start_line, start_column),
            content,
        )
    }

    /// Scan a string literal
    fn scan_string(&mut self, quote: char) -> SuiToken {
        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        self.advance(); // consume opening quote

        let mut value = String::new();
        let mut escaped = false;

        while let Some(ch) = self.peek() {
            if escaped {
                match ch {
                    'n' => value.push('\n'),
                    't' => value.push('\t'),
                    'r' => value.push('\r'),
                    '\\' => value.push('\\'),
                    '"' => value.push('"'),
                    '\'' => value.push('\''),
                    _ => {
                        value.push('\\');
                        value.push(ch);
                    }
                }
                escaped = false;
                self.advance();
            } else if ch == '\\' {
                escaped = true;
                self.advance();
            } else if ch == quote {
                self.advance();
                break;
            } else {
                if ch == '\n' {
                    self.line += 1;
                    self.column = 0;
                }
                value.push(ch);
                self.advance();
            }
        }

        SuiToken::new(
            SuiTokenKind::String(value.clone()),
            Span::new(start_pos, self.current_pos, start_line, start_column),
            value,
        )
    }

    /// Scan a number
    fn scan_number(&mut self) -> SuiToken {
        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        let mut value = String::new();
        let mut is_float = false;

        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                value.push(ch);
                self.advance();
            } else if ch == '.' && !is_float {
                // Check if it's a decimal point (not range operator)
                if self.peek_ahead(1).map_or(false, |c| c.is_ascii_digit()) {
                    is_float = true;
                    value.push(ch);
                    self.advance();
                } else {
                    break;
                }
            } else if ch == '_' {
                // Allow underscores in numbers for readability
                self.advance();
            } else {
                break;
            }
        }

        let kind = if is_float {
            match value.parse::<f64>() {
                Ok(n) => SuiTokenKind::Float(n),
                Err(_) => SuiTokenKind::Error(format!("Invalid float: {}", value)),
            }
        } else {
            match value.parse::<i64>() {
                Ok(n) => SuiTokenKind::Integer(n),
                Err(_) => SuiTokenKind::Error(format!("Invalid integer: {}", value)),
            }
        };

        self.make_token(kind, start_pos, start_line, start_column)
    }

    /// Scan an identifier or keyword
    fn scan_identifier(&mut self) -> SuiToken {
        let start_pos = self.current_pos;
        let start_line = self.line;
        let start_column = self.column;

        let mut value = String::new();

        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' || ch == '-' {
                value.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        // Check for keywords
        let kind = SuiTokenKind::keyword_from_str(&value)
            .unwrap_or_else(|| SuiTokenKind::Identifier(value.clone()));

        SuiToken::new(
            kind,
            Span::new(start_pos, self.current_pos, start_line, start_column),
            value,
        )
    }

    // Helper methods

    fn advance(&mut self) -> Option<char> {
        if let Some((pos, ch)) = self.chars.next() {
            self.current_pos = pos + ch.len_utf8();
            if ch == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
            Some(ch)
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

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch == ' ' || ch == '\t' || ch == '\r' {
                self.advance();
            } else if ch == '\n' && self.mode != LexerMode::Html {
                // In code mode, newlines are significant for multiline blocks
                break;
            } else {
                break;
            }
        }
    }

    fn make_token(
        &self,
        kind: SuiTokenKind,
        start_pos: usize,
        start_line: usize,
        start_column: usize,
    ) -> SuiToken {
        let lexeme = self.source[start_pos..self.current_pos].to_string();
        SuiToken::new(
            kind,
            Span::new(start_pos, self.current_pos, start_line, start_column),
            lexeme,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(source: &str) -> Vec<SuiTokenKind> {
        let mut lexer = SuiLexer::new(source);
        lexer.tokenize().into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn test_text_only() {
        let tokens = tokenize("Hello World");
        assert_eq!(tokens, vec![
            SuiTokenKind::Text("Hello World".to_string()),
            SuiTokenKind::Eof,
        ]);
    }

    #[test]
    fn test_output_block() {
        let tokens = tokenize("{{ name }}");
        assert_eq!(tokens, vec![
            SuiTokenKind::OutputOpen,
            SuiTokenKind::Identifier("name".to_string()),
            SuiTokenKind::OutputClose,
            SuiTokenKind::Eof,
        ]);
    }

    #[test]
    fn test_directive_block() {
        let tokens = tokenize("{@ component Counter @}");
        assert_eq!(tokens, vec![
            SuiTokenKind::DirectiveOpen,
            SuiTokenKind::Component,
            SuiTokenKind::Identifier("Counter".to_string()),
            SuiTokenKind::DirectiveClose,
            SuiTokenKind::Eof,
        ]);
    }

    #[test]
    fn test_control_if() {
        let tokens = tokenize("{% if x > 0: %}yes{% end %}");
        assert_eq!(tokens, vec![
            SuiTokenKind::ControlOpen,
            SuiTokenKind::If,
            SuiTokenKind::Identifier("x".to_string()),
            SuiTokenKind::Gt,
            SuiTokenKind::Integer(0),
            SuiTokenKind::Colon,
            SuiTokenKind::ControlClose,
            SuiTokenKind::Text("yes".to_string()),
            SuiTokenKind::ControlOpen,
            SuiTokenKind::End,
            SuiTokenKind::ControlClose,
            SuiTokenKind::Eof,
        ]);
    }

    #[test]
    fn test_html_tag() {
        let tokens = tokenize("<div class=\"foo\">");
        assert_eq!(tokens, vec![
            SuiTokenKind::TagOpen,
            SuiTokenKind::Identifier("div".to_string()),
            SuiTokenKind::Identifier("class".to_string()),
            SuiTokenKind::Assign,
            SuiTokenKind::String("foo".to_string()),
            SuiTokenKind::TagClose,
            SuiTokenKind::Eof,
        ]);
    }

    #[test]
    fn test_self_closing_tag() {
        let tokens = tokenize("<input />");
        assert_eq!(tokens, vec![
            SuiTokenKind::TagOpen,
            SuiTokenKind::Identifier("input".to_string()),
            SuiTokenKind::TagSelfClose,
            SuiTokenKind::Eof,
        ]);
    }

    #[test]
    fn test_closing_tag() {
        let tokens = tokenize("</div>");
        assert_eq!(tokens, vec![
            SuiTokenKind::TagEndOpen,
            SuiTokenKind::Identifier("div".to_string()),
            SuiTokenKind::TagClose,
            SuiTokenKind::Eof,
        ]);
    }

    #[test]
    fn test_server_block() {
        let tokens = tokenize("{- count = 0 -}");
        assert_eq!(tokens, vec![
            SuiTokenKind::ServerOpen,
            SuiTokenKind::Identifier("count".to_string()),
            SuiTokenKind::Assign,
            SuiTokenKind::Integer(0),
            SuiTokenKind::ServerClose,
            SuiTokenKind::Eof,
        ]);
    }

    #[test]
    fn test_client_block() {
        let tokens = tokenize("{+ on_click(handler) +}");
        assert_eq!(tokens, vec![
            SuiTokenKind::ClientOpen,
            SuiTokenKind::Identifier("on_click".to_string()),
            SuiTokenKind::LParen,
            SuiTokenKind::Identifier("handler".to_string()),
            SuiTokenKind::RParen,
            SuiTokenKind::ClientClose,
            SuiTokenKind::Eof,
        ]);
    }

    #[test]
    fn test_declaration_block() {
        let tokens = tokenize("{$ let count: i32 $}");
        assert_eq!(tokens, vec![
            SuiTokenKind::DeclOpen,
            SuiTokenKind::Let,
            SuiTokenKind::Identifier("count".to_string()),
            SuiTokenKind::Colon,
            SuiTokenKind::Identifier("i32".to_string()),
            SuiTokenKind::DeclClose,
            SuiTokenKind::Eof,
        ]);
    }

    #[test]
    fn test_comment_block() {
        let tokens = tokenize("{# This is a comment #}");
        assert_eq!(tokens, vec![
            SuiTokenKind::CommentOpen,
            SuiTokenKind::Comment(" This is a comment ".to_string()),
            SuiTokenKind::Eof,
        ]);
    }

    #[test]
    fn test_mixed_content() {
        let tokens = tokenize("<div>Hello {{ name }}</div>");
        assert_eq!(tokens, vec![
            SuiTokenKind::TagOpen,
            SuiTokenKind::Identifier("div".to_string()),
            SuiTokenKind::TagClose,
            SuiTokenKind::Text("Hello ".to_string()),
            SuiTokenKind::OutputOpen,
            SuiTokenKind::Identifier("name".to_string()),
            SuiTokenKind::OutputClose,
            SuiTokenKind::TagEndOpen,
            SuiTokenKind::Identifier("div".to_string()),
            SuiTokenKind::TagClose,
            SuiTokenKind::Eof,
        ]);
    }
}
