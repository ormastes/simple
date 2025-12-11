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
                } else {
                    // Otherwise it's a comment
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
                if self.check('/') {
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
                    self.advance(); // Consume the '#'
                    let next = self.peek();
                    if next == Some('[') {
                        // This is an attribute, not a comment
                        // Return a Hash token directly since we already consumed '#'
                        return Some(Token::new(
                            TokenKind::Hash,
                            Span::new(self.current_pos - 1, self.current_pos, self.line, self.column - 1),
                            "#".to_string(),
                        ));
                    }
                    // Comment line, skip to end (we already advanced past '#')
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
    fn scan_raw_string(&mut self) -> TokenKind {
        let mut value = String::new();

        while let Some(ch) = self.peek() {
            if ch == '\'' {
                self.advance();
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

        while let Some(ch) = self.peek() {
            if ch == '"' {
                // End of f-string
                self.advance();
                if !current_literal.is_empty() {
                    parts.push(FStringToken::Literal(current_literal));
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
                            if c.is_ascii_hexdigit() || c == '_' {
                                if c != '_' {
                                    num_str.push(c);
                                }
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        return match i64::from_str_radix(&num_str[2..], 16) {
                            Ok(n) => TokenKind::Integer(n),
                            Err(_) => TokenKind::Error(format!("Invalid hex number: {}", num_str)),
                        };
                    }
                    'o' | 'O' => {
                        self.advance();
                        num_str.push(ch);
                        while let Some(c) = self.peek() {
                            if ('0'..='7').contains(&c) || c == '_' {
                                if c != '_' {
                                    num_str.push(c);
                                }
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        return match i64::from_str_radix(&num_str[2..], 8) {
                            Ok(n) => TokenKind::Integer(n),
                            Err(_) => {
                                TokenKind::Error(format!("Invalid octal number: {}", num_str))
                            }
                        };
                    }
                    'b' | 'B' => {
                        self.advance();
                        num_str.push(ch);
                        while let Some(c) = self.peek() {
                            if c == '0' || c == '1' || c == '_' {
                                if c != '_' {
                                    num_str.push(c);
                                }
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        return match i64::from_str_radix(&num_str[2..], 2) {
                            Ok(n) => TokenKind::Integer(n),
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
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    fn tokenize(source: &str) -> Vec<TokenKind> {
        let mut lexer = Lexer::new(source);
        lexer.tokenize().into_iter().map(|t| t.kind).collect()
    }

    // === Literal Tests ===

    #[test]
    fn test_integer_literals() {
        assert_eq!(tokenize("42"), vec![TokenKind::Integer(42), TokenKind::Eof]);
        assert_eq!(tokenize("0"), vec![TokenKind::Integer(0), TokenKind::Eof]);
        assert_eq!(
            tokenize("1_000_000"),
            vec![TokenKind::Integer(1000000), TokenKind::Eof]
        );
    }

    #[test]
    fn test_hex_literals() {
        assert_eq!(
            tokenize("0xFF"),
            vec![TokenKind::Integer(255), TokenKind::Eof]
        );
        assert_eq!(
            tokenize("0x1A2B"),
            vec![TokenKind::Integer(0x1A2B), TokenKind::Eof]
        );
    }

    #[test]
    fn test_binary_literals() {
        assert_eq!(
            tokenize("0b1010"),
            vec![TokenKind::Integer(10), TokenKind::Eof]
        );
        assert_eq!(
            tokenize("0b1111_0000"),
            vec![TokenKind::Integer(0xF0), TokenKind::Eof]
        );
    }

    #[test]
    fn test_octal_literals() {
        assert_eq!(
            tokenize("0o77"),
            vec![TokenKind::Integer(63), TokenKind::Eof]
        );
    }

    #[test]
    fn test_float_literals() {
        assert_eq!(
            tokenize("3.14"),
            vec![TokenKind::Float(3.14), TokenKind::Eof]
        );
        assert_eq!(
            tokenize("1.0e10"),
            vec![TokenKind::Float(1.0e10), TokenKind::Eof]
        );
        assert_eq!(
            tokenize("2.5E-3"),
            vec![TokenKind::Float(2.5e-3), TokenKind::Eof]
        );
    }

    #[test]
    fn test_string_literals() {
        use crate::token::FStringToken;
        // Double-quoted strings are now FStrings (interpolated by default)
        assert_eq!(
            tokenize(r#""hello""#),
            vec![
                TokenKind::FString(vec![FStringToken::Literal("hello".to_string())]),
                TokenKind::Eof
            ]
        );
        assert_eq!(
            tokenize(r#""hello\nworld""#),
            vec![
                TokenKind::FString(vec![FStringToken::Literal("hello\nworld".to_string())]),
                TokenKind::Eof
            ]
        );
        assert_eq!(
            tokenize(r#""tab\there""#),
            vec![
                TokenKind::FString(vec![FStringToken::Literal("tab\there".to_string())]),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_raw_string_literals() {
        // Single-quoted strings are raw (no escape processing, no interpolation)
        assert_eq!(
            tokenize(r#"'hello'"#),
            vec![TokenKind::RawString("hello".to_string()), TokenKind::Eof]
        );
        // Backslashes are literal in raw strings
        assert_eq!(
            tokenize(r#"'hello\nworld'"#),
            vec![
                TokenKind::RawString("hello\\nworld".to_string()),
                TokenKind::Eof
            ]
        );
        // Braces are literal in raw strings (no interpolation)
        assert_eq!(
            tokenize(r#"'{name}'"#),
            vec![TokenKind::RawString("{name}".to_string()), TokenKind::Eof]
        );
    }

    #[test]
    fn test_interpolated_strings() {
        use crate::token::FStringToken;
        // Test interpolation in double-quoted strings
        assert_eq!(
            tokenize(r#""hello {name}""#),
            vec![
                TokenKind::FString(vec![
                    FStringToken::Literal("hello ".to_string()),
                    FStringToken::Expr("name".to_string()),
                ]),
                TokenKind::Eof
            ]
        );
        // Test escaped braces
        assert_eq!(
            tokenize(r#""literal {{braces}}""#),
            vec![
                TokenKind::FString(vec![FStringToken::Literal("literal {braces}".to_string()),]),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_bool_literals() {
        assert_eq!(
            tokenize("true"),
            vec![TokenKind::Bool(true), TokenKind::Eof]
        );
        assert_eq!(
            tokenize("false"),
            vec![TokenKind::Bool(false), TokenKind::Eof]
        );
    }

    #[test]
    fn test_nil_literal() {
        assert_eq!(tokenize("nil"), vec![TokenKind::Nil, TokenKind::Eof]);
    }

    #[test]
    fn test_symbol_literals() {
        assert_eq!(
            tokenize(":ok"),
            vec![TokenKind::Symbol("ok".to_string()), TokenKind::Eof]
        );
        assert_eq!(
            tokenize(":error_code"),
            vec![TokenKind::Symbol("error_code".to_string()), TokenKind::Eof]
        );
    }

    // === Identifier and Keyword Tests ===

    #[test]
    fn test_identifiers() {
        assert_eq!(
            tokenize("foo"),
            vec![TokenKind::Identifier("foo".to_string()), TokenKind::Eof]
        );
        assert_eq!(
            tokenize("_bar"),
            vec![TokenKind::Identifier("_bar".to_string()), TokenKind::Eof]
        );
        assert_eq!(
            tokenize("baz123"),
            vec![TokenKind::Identifier("baz123".to_string()), TokenKind::Eof]
        );
    }

    #[test]
    fn test_keywords() {
        assert_eq!(tokenize("fn"), vec![TokenKind::Fn, TokenKind::Eof]);
        assert_eq!(tokenize("let"), vec![TokenKind::Let, TokenKind::Eof]);
        assert_eq!(tokenize("if"), vec![TokenKind::If, TokenKind::Eof]);
        assert_eq!(tokenize("else"), vec![TokenKind::Else, TokenKind::Eof]);
        assert_eq!(tokenize("for"), vec![TokenKind::For, TokenKind::Eof]);
        assert_eq!(tokenize("while"), vec![TokenKind::While, TokenKind::Eof]);
        assert_eq!(tokenize("return"), vec![TokenKind::Return, TokenKind::Eof]);
        assert_eq!(tokenize("struct"), vec![TokenKind::Struct, TokenKind::Eof]);
        assert_eq!(tokenize("class"), vec![TokenKind::Class, TokenKind::Eof]);
        assert_eq!(tokenize("trait"), vec![TokenKind::Trait, TokenKind::Eof]);
        assert_eq!(tokenize("impl"), vec![TokenKind::Impl, TokenKind::Eof]);
        assert_eq!(tokenize("actor"), vec![TokenKind::Actor, TokenKind::Eof]);
        assert_eq!(tokenize("spawn"), vec![TokenKind::Spawn, TokenKind::Eof]);
    }

    // === Operator Tests ===

    #[test]
    fn test_arithmetic_operators() {
        assert_eq!(tokenize("+"), vec![TokenKind::Plus, TokenKind::Eof]);
        assert_eq!(tokenize("-"), vec![TokenKind::Minus, TokenKind::Eof]);
        assert_eq!(tokenize("*"), vec![TokenKind::Star, TokenKind::Eof]);
        assert_eq!(tokenize("/"), vec![TokenKind::Slash, TokenKind::Eof]);
        assert_eq!(tokenize("%"), vec![TokenKind::Percent, TokenKind::Eof]);
        assert_eq!(tokenize("**"), vec![TokenKind::DoubleStar, TokenKind::Eof]);
        assert_eq!(tokenize("//"), vec![TokenKind::DoubleSlash, TokenKind::Eof]);
    }

    #[test]
    fn test_comparison_operators() {
        assert_eq!(tokenize("=="), vec![TokenKind::Eq, TokenKind::Eof]);
        assert_eq!(tokenize("!="), vec![TokenKind::NotEq, TokenKind::Eof]);
        assert_eq!(tokenize("<"), vec![TokenKind::Lt, TokenKind::Eof]);
        assert_eq!(tokenize(">"), vec![TokenKind::Gt, TokenKind::Eof]);
        assert_eq!(tokenize("<="), vec![TokenKind::LtEq, TokenKind::Eof]);
        assert_eq!(tokenize(">="), vec![TokenKind::GtEq, TokenKind::Eof]);
    }

    #[test]
    fn test_assignment_operators() {
        assert_eq!(tokenize("="), vec![TokenKind::Assign, TokenKind::Eof]);
        assert_eq!(tokenize("+="), vec![TokenKind::PlusAssign, TokenKind::Eof]);
        assert_eq!(tokenize("-="), vec![TokenKind::MinusAssign, TokenKind::Eof]);
        assert_eq!(tokenize("*="), vec![TokenKind::StarAssign, TokenKind::Eof]);
        assert_eq!(tokenize("/="), vec![TokenKind::SlashAssign, TokenKind::Eof]);
    }

    #[test]
    fn test_arrow_operators() {
        assert_eq!(tokenize("->"), vec![TokenKind::Arrow, TokenKind::Eof]);
        assert_eq!(tokenize("=>"), vec![TokenKind::FatArrow, TokenKind::Eof]);
    }

    #[test]
    fn test_bitwise_operators() {
        assert_eq!(tokenize("&"), vec![TokenKind::Ampersand, TokenKind::Eof]);
        assert_eq!(tokenize("|"), vec![TokenKind::Pipe, TokenKind::Eof]);
        assert_eq!(tokenize("^"), vec![TokenKind::Caret, TokenKind::Eof]);
        assert_eq!(tokenize("~"), vec![TokenKind::Tilde, TokenKind::Eof]);
        assert_eq!(tokenize("<<"), vec![TokenKind::ShiftLeft, TokenKind::Eof]);
        assert_eq!(tokenize(">>"), vec![TokenKind::ShiftRight, TokenKind::Eof]);
    }

    // === Delimiter Tests ===

    #[test]
    fn test_delimiters() {
        assert_eq!(tokenize("("), vec![TokenKind::LParen, TokenKind::Eof]);
        assert_eq!(tokenize(")"), vec![TokenKind::RParen, TokenKind::Eof]);
        assert_eq!(tokenize("["), vec![TokenKind::LBracket, TokenKind::Eof]);
        assert_eq!(tokenize("]"), vec![TokenKind::RBracket, TokenKind::Eof]);
        assert_eq!(tokenize("{"), vec![TokenKind::LBrace, TokenKind::Eof]);
        assert_eq!(tokenize("}"), vec![TokenKind::RBrace, TokenKind::Eof]);
        assert_eq!(tokenize(","), vec![TokenKind::Comma, TokenKind::Eof]);
        assert_eq!(tokenize(":"), vec![TokenKind::Colon, TokenKind::Eof]);
        assert_eq!(tokenize("::"), vec![TokenKind::DoubleColon, TokenKind::Eof]);
        assert_eq!(tokenize("."), vec![TokenKind::Dot, TokenKind::Eof]);
        assert_eq!(tokenize(".."), vec![TokenKind::DoubleDot, TokenKind::Eof]);
        assert_eq!(tokenize("..."), vec![TokenKind::Ellipsis, TokenKind::Eof]);
    }

    // === Expression Tests ===

    #[test]
    fn test_simple_expression() {
        assert_eq!(
            tokenize("1 + 2"),
            vec![
                TokenKind::Integer(1),
                TokenKind::Plus,
                TokenKind::Integer(2),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_complex_expression() {
        assert_eq!(
            tokenize("x * (y + z)"),
            vec![
                TokenKind::Identifier("x".to_string()),
                TokenKind::Star,
                TokenKind::LParen,
                TokenKind::Identifier("y".to_string()),
                TokenKind::Plus,
                TokenKind::Identifier("z".to_string()),
                TokenKind::RParen,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_function_call() {
        assert_eq!(
            tokenize("print(x, y)"),
            vec![
                TokenKind::Identifier("print".to_string()),
                TokenKind::LParen,
                TokenKind::Identifier("x".to_string()),
                TokenKind::Comma,
                TokenKind::Identifier("y".to_string()),
                TokenKind::RParen,
                TokenKind::Eof,
            ]
        );
    }

    // === Indentation Tests ===

    #[test]
    fn test_indent_dedent() {
        let source = "if x:\n    y\nz";
        let tokens = tokenize(source);
        assert_eq!(
            tokens,
            vec![
                TokenKind::If,
                TokenKind::Identifier("x".to_string()),
                TokenKind::Colon,
                TokenKind::Newline,
                TokenKind::Indent,
                TokenKind::Identifier("y".to_string()),
                TokenKind::Newline,
                TokenKind::Dedent,
                TokenKind::Identifier("z".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_nested_indent() {
        let source = "if a:\n    if b:\n        c\nd";
        let tokens = tokenize(source);
        assert_eq!(
            tokens,
            vec![
                TokenKind::If,
                TokenKind::Identifier("a".to_string()),
                TokenKind::Colon,
                TokenKind::Newline,
                TokenKind::Indent,
                TokenKind::If,
                TokenKind::Identifier("b".to_string()),
                TokenKind::Colon,
                TokenKind::Newline,
                TokenKind::Indent,
                TokenKind::Identifier("c".to_string()),
                TokenKind::Newline,
                TokenKind::Dedent,
                TokenKind::Dedent,
                TokenKind::Identifier("d".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    // === Comment Tests ===

    #[test]
    fn test_line_comment() {
        assert_eq!(
            tokenize("x # comment\ny"),
            vec![
                TokenKind::Identifier("x".to_string()),
                TokenKind::Newline,
                TokenKind::Identifier("y".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    // === Module System Keywords Tests ===

    #[test]
    fn test_module_keywords() {
        assert_eq!(tokenize("use"), vec![TokenKind::Use, TokenKind::Eof]);
        assert_eq!(tokenize("mod"), vec![TokenKind::Mod, TokenKind::Eof]);
        assert_eq!(tokenize("export"), vec![TokenKind::Export, TokenKind::Eof]);
        assert_eq!(tokenize("common"), vec![TokenKind::Common, TokenKind::Eof]);
        assert_eq!(tokenize("auto"), vec![TokenKind::Auto, TokenKind::Eof]);
        assert_eq!(tokenize("crate"), vec![TokenKind::Crate, TokenKind::Eof]);
    }

    #[test]
    fn test_use_statement_tokens() {
        assert_eq!(
            tokenize("use crate.core.Option"),
            vec![
                TokenKind::Use,
                TokenKind::Crate,
                TokenKind::Dot,
                TokenKind::Identifier("core".to_string()),
                TokenKind::Dot,
                TokenKind::Identifier("Option".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_mod_declaration_tokens() {
        assert_eq!(
            tokenize("pub mod router"),
            vec![
                TokenKind::Pub,
                TokenKind::Mod,
                TokenKind::Identifier("router".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    // === Function Definition Test ===

    #[test]
    fn test_function_definition() {
        let source = "fn add(a: i64, b: i64) -> i64:\n    return a + b";
        let tokens = tokenize(source);
        assert_eq!(
            tokens,
            vec![
                TokenKind::Fn,
                TokenKind::Identifier("add".to_string()),
                TokenKind::LParen,
                TokenKind::Identifier("a".to_string()),
                TokenKind::Colon,
                TokenKind::Identifier("i64".to_string()),
                TokenKind::Comma,
                TokenKind::Identifier("b".to_string()),
                TokenKind::Colon,
                TokenKind::Identifier("i64".to_string()),
                TokenKind::RParen,
                TokenKind::Arrow,
                TokenKind::Identifier("i64".to_string()),
                TokenKind::Colon,
                TokenKind::Newline,
                TokenKind::Indent,
                TokenKind::Return,
                TokenKind::Identifier("a".to_string()),
                TokenKind::Plus,
                TokenKind::Identifier("b".to_string()),
                TokenKind::Dedent, // DEDENT at EOF for remaining indentation
                TokenKind::Eof,
            ]
        );
    }
}
