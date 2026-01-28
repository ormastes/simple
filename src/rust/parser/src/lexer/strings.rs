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
            } else if ch == '\\' {
                // Handle escape sequences in single-quoted raw strings
                // Only \' is treated specially (to allow single quote in string)
                // All other escapes like \n, \t are kept literally as backslash + char
                self.advance();
                if let Some(next_ch) = self.peek() {
                    if next_ch == '\'' {
                        // Escaped single quote - consume and add just the quote
                        self.advance();
                        value.push('\'');
                    } else if next_ch == '\n' {
                        // Backslash at end of line - just keep the backslash
                        // The newline will be handled in the next iteration and error
                        value.push('\\');
                    } else {
                        // All other cases: keep the backslash literal AND consume the next char
                        // This includes \\, \n, \t, \r, \0, etc.
                        // We must advance past the next char to avoid re-processing it
                        self.advance();
                        value.push('\\');
                        value.push(next_ch);
                    }
                } else {
                    // Backslash at end of file
                    value.push('\\');
                }
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
                    EscapeResult::Unterminated => return TokenKind::Error("Unterminated string".to_string()),
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
                // Check if next char is backslash - this can't be a valid expression start
                // This handles JSON patterns like {\"key\": \"value\"}
                // where { is followed by an escape sequence
                if self.check('\\') {
                    current_literal.push('{');
                    continue;
                }
                // Check if next char is a quote immediately after {
                // This handles patterns like '{' in "expected '{' after 'loss'"
                // where the user wants literal braces in the string
                if self.check('\'') || self.check('"') {
                    current_literal.push('{');
                    continue;
                }
                // Save current literal if any
                if !current_literal.is_empty() {
                    parts.push(FStringToken::Literal(current_literal));
                    current_literal = String::new();
                }
                // Read expression until }
                // Need to handle escapes and track strings inside the expression
                // Escapes like \" are translated to just " in the expression
                let mut expr = String::new();
                let mut brace_depth = 1;
                let mut in_string: Option<char> = None; // Track if inside string and which quote
                while let Some(c) = self.peek() {
                    // Handle escape sequences - translate them for the expression
                    if c == '\\' {
                        self.advance();
                        if let Some(next) = self.peek() {
                            match next {
                                '"' | '\'' => {
                                    // Escaped quote - becomes a quote in the expression
                                    self.advance();
                                    expr.push(next);
                                    // Track string state
                                    if let Some(quote) = in_string {
                                        if quote == next {
                                            in_string = None; // End string
                                        }
                                    } else {
                                        in_string = Some(next); // Start string
                                    }
                                }
                                '\\' => {
                                    // Escaped backslash - becomes single backslash
                                    self.advance();
                                    expr.push('\\');
                                }
                                'n' => {
                                    // Newline escape - keep as \n in expression
                                    self.advance();
                                    expr.push('\\');
                                    expr.push('n');
                                }
                                't' => {
                                    // Tab escape - keep as \t in expression
                                    self.advance();
                                    expr.push('\\');
                                    expr.push('t');
                                }
                                _ => {
                                    // Unknown escape - keep backslash
                                    expr.push('\\');
                                }
                            }
                        } else {
                            expr.push('\\');
                        }
                        continue;
                    }
                    // Track unescaped string boundaries
                    // For double quote: always track as string delimiter
                    // For single quote: only track as string start if NOT preceded by identifier/number/closing paren
                    // (otherwise it's the transpose operator, e.g., A' in "m{ A' @ A }")
                    if c == '"' {
                        if let Some(quote) = in_string {
                            if quote == c {
                                in_string = None; // End of string
                            }
                        } else {
                            in_string = Some(c); // Start of string
                        }
                        expr.push(c);
                        self.advance();
                        continue;
                    }
                    if c == '\'' {
                        if let Some(quote) = in_string {
                            if quote == c {
                                in_string = None; // End of string
                            }
                            expr.push(c);
                            self.advance();
                            continue;
                        } else {
                            // Check if preceded by identifier char, digit, or ')' -> transpose operator
                            let is_postfix = expr
                                .chars()
                                .last()
                                .map_or(false, |last| last.is_alphanumeric() || last == '_' || last == ')');
                            if is_postfix {
                                // This is transpose operator, not string start
                                expr.push(c);
                                self.advance();
                                continue;
                            } else {
                                // This is starting a single-quoted string
                                in_string = Some(c);
                                expr.push(c);
                                self.advance();
                                continue;
                            }
                        }
                    }
                    // Only track braces when not in a string
                    if in_string.is_none() {
                        if c == '}' {
                            brace_depth -= 1;
                            if brace_depth == 0 {
                                self.advance();
                                break;
                            }
                        } else if c == '{' {
                            brace_depth += 1;
                        }
                    }
                    expr.push(c);
                    self.advance();
                }
                if brace_depth != 0 {
                    return TokenKind::Error("Unclosed { in f-string".to_string());
                }
                // If expression is empty (just "{}"), treat as literal "{}"
                // This allows strings like "m{} block" without escaping
                if expr.trim().is_empty() {
                    current_literal.push_str("{}");
                } else {
                    parts.push(FStringToken::Expr(expr));
                    has_interpolation = true; // Mark that we have interpolation
                }
            } else if ch == '}' {
                self.advance();
                // Check for escaped }} -> literal }
                if self.check('}') {
                    self.advance();
                }
                // Treat single } as literal } (lenient mode)
                // This allows strings like "{value}}" to work where the } is part of JSON syntax
                current_literal.push('}');
            } else if ch == '\\' {
                self.advance();
                match self.process_escape(true) {
                    EscapeResult::Char(c) => current_literal.push(c),
                    EscapeResult::Error(msg) => return TokenKind::Error(msg),
                    EscapeResult::Unterminated => return TokenKind::Error("Unterminated f-string".to_string()),
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
