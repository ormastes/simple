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
    pub indent_stack: Vec<usize>,
    pub pending_tokens: Vec<Token>,
    pub at_line_start: bool,
    /// Track bracket depth to suppress INDENT/DEDENT inside delimiters
    pub bracket_depth: usize,
    /// Track previous non-whitespace token kind for disambiguation (e.g. symbol vs slice)
    prev_kind: Option<TokenKind>,
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
            prev_kind: None,
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
                    let tok = self.read_doc_line_comment(start_pos, start_line, start_column);
                    self.prev_kind = Some(tok.kind.clone());
                    return tok;
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
                // Handle literal `\n` (backslash + letter n) as line continuation
                // This appears in some Simple source files as an escape for line breaks
                if self.peek() == Some('n') {
                    // Peek further: if after `\n` we have whitespace then a keyword/ident,
                    // treat as line continuation (skip `\n` + following whitespace)
                    self.advance(); // consume the 'n'
                    // Skip any whitespace after \n
                    while self.peek() == Some(' ') || self.peek() == Some('\t') {
                        self.advance();
                    }
                    return self.next_token();
                }
                // Handle multiple consecutive backslashes (e.g., git conflict markers)
                // Skip the entire line as it's likely a conflict marker
                if self.peek() == Some('\\') {
                    while self.peek() != Some('\n') && self.peek() != None {
                        self.advance();
                    }
                    if self.peek() == Some('\n') {
                        self.advance();
                        self.line += 1;
                        self.column = 1;
                    }
                    return self.next_token();
                }
                TokenKind::Backslash
            }
            '^' => TokenKind::Caret,
            '~' => {
                if self.check('=') {
                    self.advance();
                    TokenKind::TildeAssign
                } else if self.check('>') {
                    self.advance();
                    TokenKind::TildeArrow
                } else {
                    TokenKind::Tilde
                }
            }
            '?' => {
                if self.check('?') {
                    self.advance();
                    TokenKind::DoubleQuestion
                } else {
                    TokenKind::Question
                }
            }

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
                        let tok = self.read_doc_block_comment(start_pos, start_line, start_column);
                        self.prev_kind = Some(tok.kind.clone());
                        return tok;
                    } else {
                        // Regular block comment /* ... */
                        self.skip_block_comment()
                    }
                } else if self.check('/') {
                    self.advance(); // consume second '/'
                    if self.check('/') {
                        // Doc comment /// ...
                        self.advance(); // consume third '/'
                        // Check if this is a multi-line /// block (/// on its own line)
                        // If there's only whitespace/nothing until newline, treat as multi-line delimiter
                        let is_block = {
                            let remaining = &self.source[self.current_pos..];
                            let line_rest = remaining.split('\n').next().unwrap_or("");
                            line_rest.trim().is_empty()
                        };
                        if is_block {
                            // Multi-line /// ... /// doc comment
                            // Skip to end of current line
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
                                // Check if current position starts a line with just `///`
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
                                // Read this line into content
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
                                    None => break, // EOF without closing ///
                                }
                            }
                            let tok = Token::new(
                                TokenKind::DocComment(content.trim().to_string()),
                                Span::new(start_pos, self.current_pos, start_line, start_column),
                                self.source[start_pos..self.current_pos].to_string(),
                            );
                            self.prev_kind = Some(tok.kind.clone());
                            return tok;
                        }
                        let tok = self.read_doc_line_comment(start_pos, start_line, start_column);
                        self.prev_kind = Some(tok.kind.clone());
                        return tok;
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
            '%' => self.match_char('=', TokenKind::PercentAssign, TokenKind::Percent),
            '&' => TokenKind::Ampersand,
            '|' => {
                if self.check('|') {
                    self.advance();
                    TokenKind::Or
                } else if self.check('>') {
                    self.advance();
                    TokenKind::PipeForward
                } else {
                    TokenKind::Pipe
                }
            }

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
                } else if self.check('=') {
                    self.advance();
                    TokenKind::WalrusAssign  // := (val synonym)
                } else if self.check_alpha() {
                    // Disambiguate: symbol literal :name vs colon in slice/type context
                    // If previous token was expression-ending (identifier, number, ],), etc.)
                    // then this is a colon (slice `a[0:n]`, type `x: T`, named arg `f(x: v)`)
                    let is_after_expr = matches!(
                        &self.prev_kind,
                        Some(TokenKind::Identifier(_))
                            | Some(TokenKind::Integer(_))
                            | Some(TokenKind::TypedInteger(_, _))
                            | Some(TokenKind::Float(_))
                            | Some(TokenKind::TypedFloat(_, _))
                            | Some(TokenKind::String(_))
                            | Some(TokenKind::RawString(_))
                            | Some(TokenKind::Bool(_))
                            | Some(TokenKind::Nil)
                            | Some(TokenKind::RParen)
                            | Some(TokenKind::RBracket)
                            | Some(TokenKind::RBrace)
                            | Some(TokenKind::Question)  // x?: (optional chaining)
                            | Some(TokenKind::Self_)
                            | Some(TokenKind::Super)
                    );
                    if is_after_expr {
                        TokenKind::Colon
                    } else {
                        // Symbol literal :name
                        self.scan_symbol()
                    }
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
                } else if self.peek().map_or(false, |c| c.is_ascii_digit()) && matches!(
                    &self.prev_kind,
                    None
                    | Some(TokenKind::LParen)
                    | Some(TokenKind::LBracket)
                    | Some(TokenKind::LBrace)
                    | Some(TokenKind::Comma)
                    | Some(TokenKind::Semicolon)
                    | Some(TokenKind::Colon)
                    | Some(TokenKind::Assign)
                    | Some(TokenKind::Plus)
                    | Some(TokenKind::Minus)
                    | Some(TokenKind::Star)
                    | Some(TokenKind::Slash)
                    | Some(TokenKind::Percent)
                    | Some(TokenKind::PlusAssign)
                    | Some(TokenKind::MinusAssign)
                    | Some(TokenKind::StarAssign)
                    | Some(TokenKind::SlashAssign)
                    | Some(TokenKind::Eq)
                    | Some(TokenKind::NotEq)
                    | Some(TokenKind::Lt)
                    | Some(TokenKind::Gt)
                    | Some(TokenKind::LtEq)
                    | Some(TokenKind::GtEq)
                    | Some(TokenKind::Arrow)
                    | Some(TokenKind::FatArrow)
                    | Some(TokenKind::Pipe)
                    | Some(TokenKind::PipeForward)
                    | Some(TokenKind::And)
                    | Some(TokenKind::Or)
                    | Some(TokenKind::Not)
                    | Some(TokenKind::Return)
                    | Some(TokenKind::Newline)
                    | Some(TokenKind::Indent)
                    | Some(TokenKind::Dedent)
                    | Some(TokenKind::WalrusAssign)
                ) {
                    // `.5` style float literal (no integer part) -> 0.5
                    // Only when NOT following an expression-ending token (would be member access)
                    let mut num = String::from("0.");
                    while let Some(c) = self.peek() {
                        if c.is_ascii_digit() || c == '_' {
                            num.push(c);
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    // Handle optional exponent: .5e10
                    if let Some(c) = self.peek() {
                        if c == 'e' || c == 'E' {
                            num.push(c);
                            self.advance();
                            if let Some(sign) = self.peek() {
                                if sign == '+' || sign == '-' {
                                    num.push(sign);
                                    self.advance();
                                }
                            }
                            while let Some(c) = self.peek() {
                                if c.is_ascii_digit() {
                                    num.push(c);
                                    self.advance();
                                } else {
                                    break;
                                }
                            }
                        }
                    }
                    TokenKind::Float(num.parse::<f64>().unwrap_or(0.0))
                } else {
                    TokenKind::Dot
                }
            }

            // String literals
            '"' => {
                // Check for triple-quoted string (docstring): """..."""
                if self.check('"') {
                    // Could be "" (empty) or """...""" (docstring)
                    self.advance(); // consume second "
                    if self.check('"') {
                        // Triple-quoted string: """..."""
                        self.advance(); // consume third "
                        self.scan_triple_quoted_string()
                    } else {
                        // Empty string ""
                        TokenKind::FString(vec![])
                    }
                } else {
                    self.scan_fstring() // Double quotes are interpolated by default
                }
            }
            '\'' => {
                // Check for triple-quoted raw string: '''...'''
                if self.check('\'') {
                    self.advance(); // consume second '
                    if self.check('\'') {
                        // Triple-quoted raw string: '''...'''
                        self.advance(); // consume third '
                        self.scan_triple_single_quoted_string()
                    } else {
                        // Empty raw string ''
                        TokenKind::RawString(String::new())
                    }
                } else {
                    self.scan_raw_string() // Single quotes are raw strings
                }
            }

            // Numbers
            '0'..='9' => self.scan_number(ch),

            // Identifiers and keywords
            'a'..='z' | 'A'..='Z' | '_' => self.scan_identifier(ch),

            _ => TokenKind::Error(format!("Unexpected character: '{}'", ch)),
        };

        let end_pos = self.current_pos;
        let lexeme = self.source[start_pos..end_pos].to_string();

        // Track previous token kind for disambiguation (symbol vs slice, etc.)
        self.prev_kind = Some(kind.clone());

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
