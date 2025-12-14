use crate::token::{NumericSuffix, Span, Token, TokenKind};

/// Result of processing an escape sequence
enum EscapeResult {
    /// Successfully processed escape, push this char
    Char(char),
    /// Invalid escape sequence error
    Error(String),
    /// Unterminated string (EOF after backslash)
    Unterminated,
}

pub struct Lexer<'a> {
    source: &'a str,
    chars: std::iter::Peekable<std::str::CharIndices<'a>>,
    current_pos: usize,
    line: usize,
    column: usize,
    indent_stack: Vec<usize>,
    pending_tokens: Vec<Token>,
    at_line_start: bool,
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

        // Handle indentation at line start
        if self.at_line_start {
            self.at_line_start = false;
            if let Some(indent_token) = self.handle_indentation() {
                return indent_token;
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

            // Single-character tokens
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
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
                    self.advance();
                    TokenKind::DoubleSlash
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
            '"' => self.scan_fstring(), // Double quotes are interpolated by default
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

    /// Process an escape sequence after a backslash.
    /// The backslash has already been consumed. Call after seeing '\'.
    /// If `allow_braces` is true, also handles \{ and \} escapes (for f-strings).
    fn process_escape(&mut self, allow_braces: bool) -> EscapeResult {
        match self.peek() {
            Some('n') => {
                self.advance();
                EscapeResult::Char('\n')
            }
            Some('t') => {
                self.advance();
                EscapeResult::Char('\t')
            }
            Some('r') => {
                self.advance();
                EscapeResult::Char('\r')
            }
            Some('\\') => {
                self.advance();
                EscapeResult::Char('\\')
            }
            Some('"') => {
                self.advance();
                EscapeResult::Char('"')
            }
            Some('0') => {
                self.advance();
                EscapeResult::Char('\0')
            }
            Some('{') if allow_braces => {
                self.advance();
                EscapeResult::Char('{')
            }
            Some('}') if allow_braces => {
                self.advance();
                EscapeResult::Char('}')
            }
            Some(c) => EscapeResult::Error(format!("Invalid escape sequence: \\{}", c)),
            None => EscapeResult::Unterminated,
        }
    }

    fn skip_comment(&mut self) -> TokenKind {
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

    fn skip_block_comment(&mut self) -> TokenKind {
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
                    // TODO: Could add an error token here
                    break;
                }
            }
        }
        // Return next token instead of comment
        self.next_token().kind
    }

    fn read_doc_block_comment(
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

    fn read_doc_line_comment(
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

    fn handle_indentation(&mut self) -> Option<Token> {
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
                    // At this point, peek() still returns '#' (the current char)
                    // We need to advance past '#' and then peek to see if next is '['
                    let hash_start = self.current_pos;
                    self.advance(); // Consume the '#'
                    let next = self.peek();
                    if next == Some('[') {
                        // This is an attribute, not a comment
                        // Return a Hash token directly since we already consumed '#'
                        return Some(Token::new(
                            TokenKind::Hash,
                            Span::new(
                                self.current_pos - 1,
                                self.current_pos,
                                self.line,
                                self.column - 1,
                            ),
                            "#".to_string(),
                        ));
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
                        return Some(Token::new(
                            TokenKind::DocComment(content.trim().to_string()),
                            Span::new(hash_start, self.current_pos, self.line, self.column),
                            self.source[hash_start..self.current_pos].to_string(),
                        ));
                    }
                    // Regular comment line, skip to end (we already advanced past '#')
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
                            let mut content = String::new();
                            let mut depth = 1;
                            while depth > 0 {
                                match self.advance() {
                                    Some((_, '*')) => {
                                        if self.peek() == Some('/') {
                                            self.advance();
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
                                            self.advance();
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
                            // Clean up the content
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
                            return Some(Token::new(
                                TokenKind::DocComment(cleaned),
                                Span::new(
                                    slash_start,
                                    self.current_pos,
                                    slash_start_line,
                                    slash_start_col,
                                ),
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
                        // Double slash // - return DoubleSlash token
                        self.advance(); // Consume second '/'
                        return Some(Token::new(
                            TokenKind::DoubleSlash,
                            Span::new(
                                self.current_pos - 2,
                                self.current_pos,
                                self.line,
                                self.column - 2,
                            ),
                            "//".to_string(),
                        ));
                    } else if self.peek() == Some('=') {
                        // Slash assign /=
                        self.advance(); // Consume '='
                        return Some(Token::new(
                            TokenKind::SlashAssign,
                            Span::new(
                                self.current_pos - 2,
                                self.current_pos,
                                self.line,
                                self.column - 2,
                            ),
                            "/=".to_string(),
                        ));
                    } else {
                        // Not a block comment, it's a slash token
                        // Return a Slash token directly since we already consumed '/'
                        return Some(Token::new(
                            TokenKind::Slash,
                            Span::new(
                                self.current_pos - 1,
                                self.current_pos,
                                self.line,
                                self.column - 1,
                            ),
                            "/".to_string(),
                        ));
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

    /// Scan a raw string literal (single quotes) - no escape processing or interpolation
    /// May have a unit suffix: 'value'_suffix (e.g., '/path/to/file'_file)
    fn scan_raw_string(&mut self) -> TokenKind {
        let mut value = String::new();

        while let Some(ch) = self.peek() {
            if ch == '\'' {
                self.advance();
                // Check for unit suffix after closing quote
                if let Some(suffix) = self.scan_string_unit_suffix() {
                    return TokenKind::TypedRawString(value, suffix);
                }
                return TokenKind::RawString(value);
            } else if ch == '\n' {
                return TokenKind::Error("Unterminated raw string".to_string());
            } else {
                self.advance();
                value.push(ch);
            }
        }

        TokenKind::Error("Unterminated raw string".to_string())
    }

    /// Check for and consume a unit suffix after a string literal (e.g., _ip, _file)
    /// Returns Some(suffix) if found, None otherwise
    fn scan_string_unit_suffix(&mut self) -> Option<String> {
        // Check if next char is underscore (start of unit suffix)
        if self.peek() != Some('_') {
            return None;
        }

        // Peek ahead to see if this is a valid unit suffix (_identifier)
        let mut suffix = String::new();
        let mut peek_iter = self.chars.clone();

        if let Some((_, '_')) = peek_iter.next() {
            suffix.push('_');
            // Collect the rest of the identifier
            while let Some(&(_, c)) = peek_iter.peek() {
                if c.is_alphanumeric() || c == '_' {
                    suffix.push(c);
                    peek_iter.next();
                } else {
                    break;
                }
            }
        }

        // Must have at least _X (underscore + one char)
        if suffix.len() > 1 {
            // Actually consume the suffix
            for _ in 0..suffix.len() {
                self.advance();
            }
            // Return suffix without leading underscore
            Some(suffix[1..].to_string())
        } else {
            None
        }
    }

    /// Legacy scan_string for backward compatibility (not currently used - double quotes use scan_fstring)
    #[allow(dead_code)]
    fn scan_string(&mut self) -> TokenKind {
        let mut value = String::new();

        while let Some(ch) = self.peek() {
            if ch == '"' {
                self.advance();
                return TokenKind::String(value);
            } else if ch == '\\' {
                self.advance();
                match self.process_escape(false) {
                    EscapeResult::Char(c) => value.push(c),
                    EscapeResult::Error(msg) => return TokenKind::Error(msg),
                    EscapeResult::Unterminated => {
                        return TokenKind::Error("Unterminated string".to_string())
                    }
                }
            } else if ch == '\n' {
                return TokenKind::Error("Unterminated string".to_string());
            } else {
                self.advance();
                value.push(ch);
            }
        }

        TokenKind::Error("Unterminated string".to_string())
    }

    fn scan_fstring(&mut self) -> TokenKind {
        use crate::token::FStringToken;
        let mut parts: Vec<FStringToken> = Vec::new();
        let mut current_literal = String::new();
        let mut has_interpolation = false;

        while let Some(ch) = self.peek() {
            if ch == '"' {
                // End of f-string
                self.advance();
                if !current_literal.is_empty() {
                    parts.push(FStringToken::Literal(current_literal.clone()));
                }

                // Check for unit suffix (only allowed if no interpolation)
                if !has_interpolation {
                    if let Some(suffix) = self.scan_string_unit_suffix() {
                        // Simple string with unit suffix: "127.0.0.1"_ip
                        return TokenKind::TypedString(current_literal, suffix);
                    }
                }

                return TokenKind::FString(parts);
            } else if ch == '{' {
                self.advance();
                // Check for escaped {{ -> literal {
                if self.check('{') {
                    self.advance();
                    current_literal.push('{');
                    continue;
                }
                // Save current literal if any
                if !current_literal.is_empty() {
                    parts.push(FStringToken::Literal(current_literal));
                    current_literal = String::new();
                }
                // Read expression until }
                let mut expr = String::new();
                let mut brace_depth = 1;
                while let Some(c) = self.peek() {
                    if c == '}' {
                        brace_depth -= 1;
                        if brace_depth == 0 {
                            self.advance();
                            break;
                        }
                    } else if c == '{' {
                        brace_depth += 1;
                    }
                    expr.push(c);
                    self.advance();
                }
                if brace_depth != 0 {
                    return TokenKind::Error("Unclosed { in f-string".to_string());
                }
                parts.push(FStringToken::Expr(expr));
                has_interpolation = true; // Mark that we have interpolation
            } else if ch == '}' {
                self.advance();
                // Check for escaped }} -> literal }
                if self.check('}') {
                    self.advance();
                    current_literal.push('}');
                } else {
                    return TokenKind::Error("Single } in f-string (use }} to escape)".to_string());
                }
            } else if ch == '\\' {
                self.advance();
                match self.process_escape(true) {
                    EscapeResult::Char(c) => current_literal.push(c),
                    EscapeResult::Error(msg) => return TokenKind::Error(msg),
                    EscapeResult::Unterminated => {
                        return TokenKind::Error("Unterminated f-string".to_string())
                    }
                }
            } else if ch == '\n' {
                return TokenKind::Error("Unterminated f-string".to_string());
            } else {
                self.advance();
                current_literal.push(ch);
            }
        }

        TokenKind::Error("Unterminated f-string".to_string())
    }

    fn scan_number(&mut self, first: char) -> TokenKind {
        let mut num_str = String::from(first);
        let mut is_float = false;

        // Handle hex, octal, binary
        if first == '0' {
            if let Some(ch) = self.peek() {
                match ch {
                    'x' | 'X' => {
                        self.advance();
                        num_str.push(ch);
                        while let Some(c) = self.peek() {
                            if c.is_ascii_hexdigit() {
                                num_str.push(c);
                                self.advance();
                            } else if c == '_' {
                                // Look ahead: if underscore is followed by letter (unit suffix), stop
                                let mut peek_ahead = self.chars.clone();
                                peek_ahead.next(); // skip '_'
                                if let Some((_, next)) = peek_ahead.next() {
                                    if next.is_alphabetic() && !next.is_ascii_hexdigit() {
                                        // This is a unit suffix like _ip, stop number parsing
                                        break;
                                    }
                                }
                                // Otherwise it's a digit separator, consume and skip
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        return match i64::from_str_radix(&num_str[2..], 16) {
                            Ok(n) => {
                                // Check for unit suffix
                                if let Some(suffix) = self.scan_numeric_suffix() {
                                    TokenKind::TypedInteger(n, suffix)
                                } else {
                                    TokenKind::Integer(n)
                                }
                            }
                            Err(_) => TokenKind::Error(format!("Invalid hex number: {}", num_str)),
                        };
                    }
                    'o' | 'O' => {
                        self.advance();
                        num_str.push(ch);
                        while let Some(c) = self.peek() {
                            if ('0'..='7').contains(&c) {
                                num_str.push(c);
                                self.advance();
                            } else if c == '_' {
                                // Look ahead: if underscore is followed by letter (unit suffix), stop
                                let mut peek_ahead = self.chars.clone();
                                peek_ahead.next(); // skip '_'
                                if let Some((_, next)) = peek_ahead.next() {
                                    if next.is_alphabetic() {
                                        // This is a unit suffix like _ip, stop number parsing
                                        break;
                                    }
                                }
                                // Otherwise it's a digit separator, consume and skip
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        return match i64::from_str_radix(&num_str[2..], 8) {
                            Ok(n) => {
                                // Check for unit suffix
                                if let Some(suffix) = self.scan_numeric_suffix() {
                                    TokenKind::TypedInteger(n, suffix)
                                } else {
                                    TokenKind::Integer(n)
                                }
                            }
                            Err(_) => {
                                TokenKind::Error(format!("Invalid octal number: {}", num_str))
                            }
                        };
                    }
                    'b' | 'B' => {
                        self.advance();
                        num_str.push(ch);
                        while let Some(c) = self.peek() {
                            if c == '0' || c == '1' {
                                num_str.push(c);
                                self.advance();
                            } else if c == '_' {
                                // Look ahead: if underscore is followed by letter (unit suffix), stop
                                let mut peek_ahead = self.chars.clone();
                                peek_ahead.next(); // skip '_'
                                if let Some((_, next)) = peek_ahead.next() {
                                    if next.is_alphabetic() {
                                        // This is a unit suffix like _ip, stop number parsing
                                        break;
                                    }
                                }
                                // Otherwise it's a digit separator, consume and skip
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        return match i64::from_str_radix(&num_str[2..], 2) {
                            Ok(n) => {
                                // Check for unit suffix
                                if let Some(suffix) = self.scan_numeric_suffix() {
                                    TokenKind::TypedInteger(n, suffix)
                                } else {
                                    TokenKind::Integer(n)
                                }
                            }
                            Err(_) => {
                                TokenKind::Error(format!("Invalid binary number: {}", num_str))
                            }
                        };
                    }
                    _ => {}
                }
            }
        }

        // Regular decimal number
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                num_str.push(ch);
                self.advance();
            } else if ch == '_' {
                // Look ahead: if underscore is followed by letter (unit suffix), stop
                let mut peek_ahead = self.chars.clone();
                peek_ahead.next(); // skip '_'
                if let Some((_, next)) = peek_ahead.next() {
                    if next.is_alphabetic() {
                        // This is a unit suffix like _km, stop number parsing
                        break;
                    }
                }
                // Otherwise it's a digit separator, consume and skip
                self.advance();
            } else {
                break;
            }
        }

        // Check for float
        if self.check('.') {
            // Look ahead to distinguish 1.2 from 1..2
            let mut peek_iter = self.chars.clone();
            peek_iter.next(); // skip '.'
            if let Some((_, next_ch)) = peek_iter.next() {
                if next_ch.is_ascii_digit() {
                    is_float = true;
                    self.advance(); // consume '.'
                    num_str.push('.');

                    while let Some(ch) = self.peek() {
                        if ch.is_ascii_digit() {
                            num_str.push(ch);
                            self.advance();
                        } else if ch == '_' {
                            // Look ahead: if underscore is followed by letter (unit suffix), stop
                            let mut peek_ahead = self.chars.clone();
                            peek_ahead.next(); // skip '_'
                            if let Some((_, next)) = peek_ahead.next() {
                                if next.is_alphabetic() {
                                    break;
                                }
                            }
                            self.advance();
                        } else {
                            break;
                        }
                    }
                }
            }
        }

        // Check for exponent
        if let Some(ch) = self.peek() {
            if ch == 'e' || ch == 'E' {
                is_float = true;
                self.advance();
                num_str.push(ch);

                if let Some(sign) = self.peek() {
                    if sign == '+' || sign == '-' {
                        self.advance();
                        num_str.push(sign);
                    }
                }

                while let Some(c) = self.peek() {
                    if c.is_ascii_digit() {
                        num_str.push(c);
                        self.advance();
                    } else {
                        break;
                    }
                }
            }
        }

        // Check for type suffix
        let suffix = self.scan_numeric_suffix();

        if is_float {
            match num_str.parse::<f64>() {
                Ok(n) => {
                    if let Some(s) = suffix {
                        TokenKind::TypedFloat(n, s)
                    } else {
                        TokenKind::Float(n)
                    }
                }
                Err(_) => TokenKind::Error(format!("Invalid float: {}", num_str)),
            }
        } else {
            match num_str.parse::<i64>() {
                Ok(n) => {
                    if let Some(s) = suffix {
                        TokenKind::TypedInteger(n, s)
                    } else {
                        TokenKind::Integer(n)
                    }
                }
                Err(_) => TokenKind::Error(format!("Invalid integer: {}", num_str)),
            }
        }
    }

    fn scan_numeric_suffix(&mut self) -> Option<NumericSuffix> {
        // Check for type suffix: i8, i16, i32, i64, u8, u16, u32, u64, f32, f64
        // Or user-defined unit suffix starting with _ like _km, _hr
        let mut suffix = String::new();

        // Peek ahead to see if we have a suffix
        let mut peek_iter = self.chars.clone();
        if let Some((_, ch)) = peek_iter.peek() {
            if *ch == 'i' || *ch == 'u' || *ch == 'f' || *ch == '_' {
                // Collect the suffix
                while let Some(&(_, c)) = peek_iter.peek() {
                    if c.is_alphanumeric() || c == '_' {
                        suffix.push(c);
                        peek_iter.next();
                    } else {
                        break;
                    }
                }
            }
        }

        // Check if it's a valid suffix
        let result = match suffix.as_str() {
            "i8" => Some(NumericSuffix::I8),
            "i16" => Some(NumericSuffix::I16),
            "i32" => Some(NumericSuffix::I32),
            "i64" => Some(NumericSuffix::I64),
            "u8" => Some(NumericSuffix::U8),
            "u16" => Some(NumericSuffix::U16),
            "u32" => Some(NumericSuffix::U32),
            "u64" => Some(NumericSuffix::U64),
            "f32" => Some(NumericSuffix::F32),
            "f64" => Some(NumericSuffix::F64),
            s if s.starts_with('_') && s.len() > 1 => {
                // User-defined unit suffix (e.g., _km, _hr)
                Some(NumericSuffix::Unit(s[1..].to_string()))
            }
            _ => None,
        };

        // Actually consume the suffix if valid
        if result.is_some() {
            for _ in 0..suffix.len() {
                self.advance();
            }
        }

        result
    }

    fn scan_identifier(&mut self, first: char) -> TokenKind {
        // Check for f-string: f"..."
        if first == 'f' && self.check('"') {
            self.advance(); // consume the opening "
            return self.scan_fstring();
        }

        let mut name = String::from(first);

        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                name.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        // Check for keywords
        match name.as_str() {
            "fn" => TokenKind::Fn,
            "let" => TokenKind::Let,
            "mut" => TokenKind::Mut,
            "if" => TokenKind::If,
            "elif" => TokenKind::Elif,
            "else" => TokenKind::Else,
            "for" => TokenKind::For,
            "while" => TokenKind::While,
            "loop" => TokenKind::Loop,
            "break" => TokenKind::Break,
            "continue" => TokenKind::Continue,
            "return" => TokenKind::Return,
            "match" => TokenKind::Match,
            "case" => TokenKind::Case,
            "struct" => TokenKind::Struct,
            "class" => TokenKind::Class,
            "enum" => TokenKind::Enum,
            "trait" => TokenKind::Trait,
            "impl" => TokenKind::Impl,
            "actor" => TokenKind::Actor,
            "pub" => TokenKind::Pub,
            "priv" => TokenKind::Priv,
            "import" => TokenKind::Import,
            "from" => TokenKind::From,
            "as" => TokenKind::As,
            "mod" => TokenKind::Mod,
            "use" => TokenKind::Use,
            "export" => TokenKind::Export,
            "common" => TokenKind::Common,
            "auto" => TokenKind::Auto,
            "crate" => TokenKind::Crate,
            "in" => TokenKind::In,
            "is" => TokenKind::Is,
            "not" => TokenKind::Not,
            "and" => TokenKind::And,
            "or" => TokenKind::Or,
            "true" => TokenKind::Bool(true),
            "false" => TokenKind::Bool(false),
            "nil" => TokenKind::Nil,
            "spawn" => TokenKind::Spawn,
            "new" => TokenKind::New,
            "self" => TokenKind::Self_,
            "super" => TokenKind::Super,
            "async" => TokenKind::Async,
            "await" => TokenKind::Await,
            "yield" => TokenKind::Yield,
            "move" => TokenKind::Move,
            "const" => TokenKind::Const,
            "static" => TokenKind::Static,
            "type" => TokenKind::Type,
            "unit" => TokenKind::Unit,
            "extern" => TokenKind::Extern,
            "context" => TokenKind::Context,
            "with" => TokenKind::With,
            "macro" => TokenKind::Macro,
            "vec" => TokenKind::Vec,
            "shared" => TokenKind::Shared,
            "gpu" => TokenKind::Gpu,
            "requires" => TokenKind::Requires,
            "ensures" => TokenKind::Ensures,
            "invariant" => TokenKind::Invariant,
            "old" => TokenKind::Old,
            "_" => TokenKind::Underscore,
            _ => TokenKind::Identifier(name),
        }
    }

    fn scan_symbol(&mut self) -> TokenKind {
        let mut name = String::new();

        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                name.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        if name.is_empty() {
            TokenKind::Colon
        } else {
            TokenKind::Symbol(name)
        }
    }
}

#[cfg(test)]
#[path = "lexer_tests.rs"]
mod tests;
