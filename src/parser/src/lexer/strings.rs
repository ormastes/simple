use super::escapes::EscapeResult;
use crate::token::TokenKind;

impl<'a> super::Lexer<'a> {
    pub(super) fn scan_raw_string(&mut self) -> TokenKind {
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

    /// Scan a raw double-quoted string: r"..." - no escapes, no interpolation
    /// Similar to single-quoted strings but with double quotes
    pub(super) fn scan_raw_double_string(&mut self) -> TokenKind {
        let mut value = String::new();

        while let Some(ch) = self.peek() {
            if ch == '"' {
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
    pub(super) fn scan_string_unit_suffix(&mut self) -> Option<String> {
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
    pub(super) fn scan_string(&mut self) -> TokenKind {
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

    /// Scan a triple-quoted string (docstring): """..."""
    /// These are raw strings that can span multiple lines and don't support interpolation
    pub(super) fn scan_triple_quoted_string(&mut self) -> TokenKind {
        let mut value = String::new();

        // Consume the three opening quotes
        self.advance(); // First "
        self.advance(); // Second "
                        // Third " was already consumed in scan_token

        // Read until we find three closing quotes
        while let Some(ch) = self.peek() {
            if ch == '"' {
                // Check for potential closing """
                if self.peek_ahead(1) == Some('"') && self.peek_ahead(2) == Some('"') {
                    // Found closing """
                    self.advance(); // First "
                    self.advance(); // Second "
                    self.advance(); // Third "
                    return TokenKind::String(value);
                } else {
                    // Single " inside the string
                    self.advance();
                    value.push('"');
                }
            } else {
                // Regular character (including newlines)
                self.advance();
                value.push(ch);
            }
        }

        TokenKind::Error("Unterminated triple-quoted string".to_string())
    }

    pub(super) fn scan_fstring(&mut self) -> TokenKind {
        self.scan_fstring_impl(false)
    }

    /// Scan a triple-quoted f-string: f"""..."""
    /// Multi-line interpolated string with escape sequence support
    pub(super) fn scan_triple_fstring(&mut self) -> TokenKind {
        // Consume the three opening quotes (first " already consumed by caller)
        self.advance(); // Second "
        self.advance(); // Third "
        self.scan_fstring_impl(true)
    }

    /// Common implementation for f-strings (single and triple-quoted)
    fn scan_fstring_impl(&mut self, is_triple: bool) -> TokenKind {
        use crate::token::FStringToken;
        let mut parts: Vec<FStringToken> = Vec::new();
        let mut current_literal = String::new();
        let mut has_interpolation = false;

        while let Some(ch) = self.peek() {
            if ch == '"' {
                if is_triple {
                    // Check for closing """
                    if self.peek_ahead(1) == Some('"') && self.peek_ahead(2) == Some('"') {
                        // Found closing """
                        self.advance(); // First "
                        self.advance(); // Second "
                        self.advance(); // Third "
                        if !current_literal.is_empty() {
                            parts.push(FStringToken::Literal(current_literal));
                        }
                        return TokenKind::FString(parts);
                    } else {
                        // Single " inside the string - treat as literal
                        self.advance();
                        current_literal.push('"');
                        continue;
                    }
                } else {
                    // End of single-quoted f-string
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
                }
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
                if is_triple {
                    // Newlines are allowed in triple-quoted f-strings
                    self.advance();
                    current_literal.push(ch);
                } else {
                    return TokenKind::Error("Unterminated f-string".to_string());
                }
            } else {
                self.advance();
                current_literal.push(ch);
            }
        }

        if is_triple {
            TokenKind::Error("Unterminated triple-quoted f-string".to_string())
        } else {
            TokenKind::Error("Unterminated f-string".to_string())
        }
    }
}
