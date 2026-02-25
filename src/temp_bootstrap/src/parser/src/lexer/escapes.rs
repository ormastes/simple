/// Result of processing an escape sequence
pub(super) enum EscapeResult {
    /// Successfully processed escape, push this char
    Char(char),
    /// Successfully processed escape, push these chars (for multi-char escapes like \uXXXX)
    Chars(Vec<char>),
    /// Invalid escape sequence error
    #[allow(dead_code)] // Matched in strings.rs but not currently constructed; kept for future error-strict mode
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
            Some('{') if allow_braces => {
                self.advance();
                EscapeResult::Char('{')
            }
            Some('}') if allow_braces => {
                self.advance();
                EscapeResult::Char('}')
            }
            Some('u') => {
                // Unicode escape: \uXXXX (4 hex digits) or \u{XXXX}
                self.advance(); // consume 'u'
                // Collect hex digits
                let mut hex = String::new();
                // Check for \u{XXXX} form
                if self.peek() == Some('{') {
                    self.advance(); // consume '{'
                    while let Some(c) = self.peek() {
                        if c == '}' {
                            self.advance();
                            break;
                        }
                        if c.is_ascii_hexdigit() {
                            hex.push(c);
                            self.advance();
                        } else {
                            break;
                        }
                    }
                } else {
                    // \uXXXX form: read up to 4 hex digits
                    for _ in 0..4 {
                        if let Some(c) = self.peek() {
                            if c.is_ascii_hexdigit() {
                                hex.push(c);
                                self.advance();
                            } else {
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                }
                if hex.is_empty() {
                    // Just \u with nothing after -- treat as literal \u
                    EscapeResult::Chars(vec!['\\', 'u'])
                } else if let Ok(code) = u32::from_str_radix(&hex, 16) {
                    if let Some(ch) = char::from_u32(code) {
                        EscapeResult::Char(ch)
                    } else {
                        // Invalid Unicode code point -- treat as literal
                        let mut chars = vec!['\\', 'u'];
                        chars.extend(hex.chars());
                        EscapeResult::Chars(chars)
                    }
                } else {
                    // Invalid hex -- treat as literal
                    let mut chars = vec!['\\', 'u'];
                    chars.extend(hex.chars());
                    EscapeResult::Chars(chars)
                }
            }
            Some('x') => {
                // Hex escape: \xXX
                self.advance(); // consume 'x'
                let mut hex = String::new();
                for _ in 0..2 {
                    if let Some(c) = self.peek() {
                        if c.is_ascii_hexdigit() {
                            hex.push(c);
                            self.advance();
                        } else {
                            break;
                        }
                    }
                }
                if hex.is_empty() {
                    EscapeResult::Chars(vec!['\\', 'x'])
                } else if let Ok(byte) = u8::from_str_radix(&hex, 16) {
                    EscapeResult::Char(byte as char)
                } else {
                    let mut chars = vec!['\\', 'x'];
                    chars.extend(hex.chars());
                    EscapeResult::Chars(chars)
                }
            }
            Some(c) => {
                // Unknown escape sequence: treat as literal backslash + char
                // (matching Simple's original lexer behavior)
                self.advance();
                EscapeResult::Chars(vec!['\\', c])
            }
            None => EscapeResult::Unterminated,
        }
    }
}
