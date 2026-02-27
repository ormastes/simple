/// Result of processing an escape sequence
pub(super) enum EscapeResult {
    /// Successfully processed escape, push this char
    Char(char),
    /// Invalid escape sequence error
    Error(String),
    /// Unterminated string (EOF after backslash)
    Unterminated,
}

impl<'a> super::Lexer<'a> {
    pub(super) fn process_escape(&mut self, allow_braces: bool) -> EscapeResult {
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
            Some('\'') => {
                self.advance();
                EscapeResult::Char('\'')
            }
            Some('0') => {
                self.advance();
                EscapeResult::Char('\0')
            }
            Some('a') => {
                self.advance();
                EscapeResult::Char('\x07') // bell
            }
            Some('b') => {
                self.advance();
                EscapeResult::Char('\x08') // backspace
            }
            Some('f') => {
                self.advance();
                EscapeResult::Char('\x0C') // form feed
            }
            Some('v') => {
                self.advance();
                EscapeResult::Char('\x0B') // vertical tab
            }
            Some('x') => {
                // Hex escape: \xNN (2 hex digits)
                self.advance(); // consume 'x'
                self.process_hex_escape()
            }
            Some('u') => {
                // Unicode escape: \uNNNN (4 hex digits) or \u{NNNNNN} (1-6 hex digits)
                self.advance(); // consume 'u'
                self.process_unicode_escape()
            }
            Some('{') if allow_braces => {
                self.advance();
                EscapeResult::Char('{')
            }
            Some('}') if allow_braces => {
                self.advance();
                EscapeResult::Char('}')
            }
            // Allow \: as literal colon (used in format strings)
            Some(':') => {
                self.advance();
                EscapeResult::Char(':')
            }
            // Allow \/ as literal slash (used in regex/path patterns)
            Some('/') => {
                self.advance();
                EscapeResult::Char('/')
            }
            // Allow \. as literal dot
            Some('.') => {
                self.advance();
                EscapeResult::Char('.')
            }
            // Allow \- as literal dash
            Some('-') => {
                self.advance();
                EscapeResult::Char('-')
            }
            // Treat unknown escape sequences as literal characters (e.g., \U, \P, \w, \d)
            // This matches Python/Simple behavior where unknown escapes pass through
            Some(c) => {
                self.advance();
                EscapeResult::Char(c)
            }
            None => EscapeResult::Unterminated,
        }
    }

    /// Process hex escape: \xNN (exactly 2 hex digits)
    fn process_hex_escape(&mut self) -> EscapeResult {
        let mut hex = String::new();
        for _ in 0..2 {
            match self.peek() {
                Some(c) if c.is_ascii_hexdigit() => {
                    hex.push(c);
                    self.advance();
                }
                _ => {
                    // Allow partial hex - treat as literal if not enough digits
                    if hex.is_empty() {
                        return EscapeResult::Error("Invalid hex escape: \\x requires hex digits".to_string());
                    }
                    break;
                }
            }
        }
        match u32::from_str_radix(&hex, 16) {
            Ok(code) => match char::from_u32(code) {
                Some(c) => EscapeResult::Char(c),
                None => EscapeResult::Error(format!("Invalid hex escape: \\x{} is not a valid character", hex)),
            },
            Err(_) => EscapeResult::Error(format!("Invalid hex escape: \\x{}", hex)),
        }
    }

    /// Process unicode escape: \uNNNN (4 hex digits) or \u{N...} (1-6 hex digits in braces)
    fn process_unicode_escape(&mut self) -> EscapeResult {
        if self.peek() == Some('{') {
            // Braced form: \u{NNNNNN}
            self.advance(); // consume '{'
            let mut hex = String::new();
            while let Some(c) = self.peek() {
                if c == '}' {
                    self.advance();
                    break;
                }
                if c.is_ascii_hexdigit() && hex.len() < 6 {
                    hex.push(c);
                    self.advance();
                } else {
                    return EscapeResult::Error(format!("Invalid unicode escape: \\u{{{}}}", hex));
                }
            }
            match u32::from_str_radix(&hex, 16) {
                Ok(code) => match char::from_u32(code) {
                    Some(c) => EscapeResult::Char(c),
                    None => EscapeResult::Error(format!("Invalid unicode code point: U+{:04X}", code)),
                },
                Err(_) => EscapeResult::Error(format!("Invalid unicode escape: \\u{{{}}}", hex)),
            }
        } else {
            // Fixed-width form: \uNNNN (exactly 4 hex digits)
            let mut hex = String::new();
            for _ in 0..4 {
                match self.peek() {
                    Some(c) if c.is_ascii_hexdigit() => {
                        hex.push(c);
                        self.advance();
                    }
                    _ => {
                        if hex.is_empty() {
                            return EscapeResult::Error("Invalid unicode escape: \\u requires hex digits".to_string());
                        }
                        break;
                    }
                }
            }
            match u32::from_str_radix(&hex, 16) {
                Ok(code) => match char::from_u32(code) {
                    Some(c) => EscapeResult::Char(c),
                    None => EscapeResult::Error(format!("Invalid unicode code point: U+{:04X}", code)),
                },
                Err(_) => EscapeResult::Error(format!("Invalid unicode escape: \\u{}", hex)),
            }
        }
    }
}
