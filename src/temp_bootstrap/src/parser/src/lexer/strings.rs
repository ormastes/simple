use crate::token::TokenKind;
use super::escapes::EscapeResult;

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
                self.advance();
                // In raw strings, \' is an escaped single quote, \\ is a literal backslash.
                // Everything else: backslash is literal.
                if let Some(next) = self.peek() {
                    if next == '\'' {
                        self.advance();
                        value.push('\'');
                    } else if next == '\\' {
                        // \\ -> literal backslash (consume second \ so it's not re-processed)
                        self.advance();
                        value.push('\\');
                        value.push('\\');
                    } else {
                        // Keep the backslash as literal
                        value.push('\\');
                        // Don't consume the next char here -- let the loop handle it
                    }
                } else {
                    value.push('\\');
                }
            } else if ch == '\n' {
                // Allow multi-line raw strings
                self.advance();
                self.line += 1;
                self.column = 0;
                value.push('\n');
            } else {
                self.advance();
                value.push(ch);
            }
        }

        TokenKind::Error("Unterminated raw string".to_string())
    }

    /// Scan a raw double-quoted string: r"..."
    /// No escape processing, no interpolation. Only \" is special (escaped double quote).
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
            } else if ch == '\\' {
                self.advance();
                // In raw strings, only \" is special (escaped double quote)
                // Everything else is kept as-is (literal backslash + char)
                if let Some(next) = self.peek() {
                    if next == '"' {
                        self.advance();
                        value.push('"');
                    } else {
                        value.push('\\');
                    }
                } else {
                    value.push('\\');
                }
            } else if ch == '\n' {
                // Allow multi-line raw strings
                self.advance();
                self.line += 1;
                self.column = 0;
                value.push('\n');
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
                    EscapeResult::Chars(chars) => {
                        for c in chars {
                            value.push(c);
                        }
                    }
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

    /// Scan a triple-single-quoted string: '''...'''
    /// Used for raw multi-line strings in Simple. No escapes, no interpolation.
    pub(super) fn scan_triple_single_quoted_string(&mut self) -> TokenKind {
        let mut value = String::new();
        let mut consecutive_quotes = 0;

        while let Some(ch) = self.peek() {
            if ch == '\'' {
                consecutive_quotes += 1;
                self.advance();
                if consecutive_quotes >= 3 {
                    // Remove the trailing quotes from value
                    if value.len() >= 2 {
                        value.truncate(value.len() - 2);
                    }
                    return TokenKind::RawString(value);
                }
                value.push(ch);
            } else {
                consecutive_quotes = 0;
                if ch == '\n' {
                    self.line += 1;
                    self.column = 0;
                }
                self.advance();
                value.push(ch);
            }
        }

        TokenKind::Error("Unterminated triple-quoted raw string".to_string())
    }

    /// Scan a triple-quoted string: """..."""
    /// Used for docstrings in Simple. Treated as a DocComment token.
    pub(super) fn scan_triple_quoted_string(&mut self) -> TokenKind {
        let mut value = String::new();
        let mut consecutive_quotes = 0;

        while let Some(ch) = self.peek() {
            if ch == '"' {
                consecutive_quotes += 1;
                self.advance();
                if consecutive_quotes >= 3 {
                    // Remove the trailing quotes from value
                    // We've accumulated 2 quotes in value before the 3rd
                    if value.len() >= 2 {
                        value.truncate(value.len() - 2);
                    }
                    return TokenKind::DocComment(value.trim().to_string());
                }
                value.push(ch);
            } else {
                consecutive_quotes = 0;
                if ch == '\n' {
                    self.line += 1;
                    self.column = 0;
                }
                self.advance();
                value.push(ch);
            }
        }

        TokenKind::Error("Unterminated triple-quoted string".to_string())
    }

    /// Scan a triple-quoted raw string: r"""..."""
    /// Similar to scan_triple_quoted_string but returns a DocComment token
    pub(super) fn scan_triple_single_quoted_string_like(&mut self) -> TokenKind {
        let mut value = String::new();
        let mut consecutive_quotes = 0;

        while let Some(ch) = self.peek() {
            if ch == '"' {
                consecutive_quotes += 1;
                self.advance();
                if consecutive_quotes >= 3 {
                    // Remove the trailing quotes from value
                    if value.len() >= 2 {
                        value.truncate(value.len() - 2);
                    }
                    return TokenKind::DocComment(value.trim().to_string());
                }
                value.push(ch);
            } else {
                consecutive_quotes = 0;
                if ch == '\n' {
                    self.line += 1;
                    self.column = 0;
                }
                self.advance();
                value.push(ch);
            }
        }

        TokenKind::Error("Unterminated raw triple-quoted string".to_string())
    }

    pub(super) fn scan_fstring(&mut self) -> TokenKind {
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

                // Check if this { can start an interpolation expression.
                // If the next char is } or " (closing string immediately),
                // treat { as a literal character.
                if self.check('"') || self.check('\n') {
                    // Lone { at end of string or before newline -- treat as literal
                    current_literal.push('{');
                    continue;
                }
                // If { is followed by \ and then " (e.g., {\"name\"}), this is
                // a JSON string pattern, not an interpolation. Treat { as literal.
                if self.check('\\') {
                    if self.peek_ahead(1) == Some('"') {
                        current_literal.push('{');
                        continue;
                    }
                }
                if self.check('}') {
                    // {} is an empty expression -- treat as literal {}
                    self.advance();
                    current_literal.push('{');
                    current_literal.push('}');
                    continue;
                }

                // Save current literal if any
                if !current_literal.is_empty() {
                    parts.push(FStringToken::Literal(current_literal));
                    current_literal = String::new();
                }
                // Read expression until matching }
                // In Simple, \" inside {expr} is an escaped quote (part of the f-string escape),
                // not a string delimiter inside the expression. So we skip \" pairs.
                let mut expr = String::new();
                let mut brace_depth = 1;
                while let Some(c) = self.peek() {
                    if c == '\\' {
                        // Escape sequence inside f-string expression.
                        // In Simple, \" inside {expr} is an f-string escape for a literal quote.
                        // We resolve it here so the sub-parser sees the actual characters.
                        self.advance(); // consume backslash
                        if let Some(nc) = self.peek() {
                            match nc {
                                '"' => {
                                    // \" -> literal " in the expression
                                    expr.push('"');
                                    self.advance();
                                }
                                '\\' => {
                                    // \\ -> literal \ in the expression
                                    expr.push('\\');
                                    self.advance();
                                }
                                '{' => {
                                    // \{ -> literal { in the expression
                                    expr.push('{');
                                    self.advance();
                                }
                                '}' => {
                                    // \} -> literal } in the expression
                                    expr.push('}');
                                    self.advance();
                                }
                                'n' => {
                                    // \n -> keep as \n for the sub-parser
                                    expr.push('\\');
                                    expr.push('n');
                                    self.advance();
                                }
                                't' => {
                                    expr.push('\\');
                                    expr.push('t');
                                    self.advance();
                                }
                                _ => {
                                    // Unknown escape: keep backslash and char
                                    expr.push('\\');
                                    expr.push(nc);
                                    self.advance();
                                }
                            }
                        } else {
                            expr.push('\\');
                        }
                        continue;
                    }
                    if c == '"' {
                        // Check if this " starts a string literal inside the expression.
                        // e.g., {items.join(", ")} — the ", " is a string arg.
                        // We scan forward with lookahead first: if we find a closing "
                        // before } or newline, AND the closing } appears after the inner
                        // string closes, it's a string literal inside the expression;
                        // otherwise it's the f-string closer — do NOT consume it.
                        let mut lookahead = self.chars.clone();
                        lookahead.next(); // skip the opening "
                        let mut has_matching_close = false;
                        let mut inner_brace_depth: i32 = 0;
                        loop {
                            match lookahead.next() {
                                Some((_, '"')) => { has_matching_close = true; break; }
                                Some((_, '\\')) => { lookahead.next(); } // skip escape
                                Some((_, '{')) => { inner_brace_depth += 1; }
                                Some((_, '}')) => {
                                    if inner_brace_depth > 0 {
                                        inner_brace_depth -= 1;
                                    } else {
                                        // } would close the interpolation before the inner
                                        // string closes — this " is the f-string closer.
                                        break;
                                    }
                                }
                                Some((_, '\n')) | None => { break; }
                                _ => {}
                            }
                        }
                        if !has_matching_close {
                            // This " is the f-string closer, not an inner string.
                            // Don't consume it — break out of expression scanning.
                            break;
                        }
                        // It's a real inner string — consume and add to expr
                        self.advance(); // consume opening "
                        expr.push('"');
                        while let Some(sc) = self.peek() {
                            if sc == '\\' {
                                // Escape inside inner string
                                expr.push(sc);
                                self.advance();
                                if let Some(esc) = self.peek() {
                                    expr.push(esc);
                                    self.advance();
                                }
                                continue;
                            }
                            if sc == '"' {
                                // Closing quote of inner string
                                expr.push('"');
                                self.advance();
                                break;
                            }
                            if sc == '\n' {
                                break;
                            }
                            expr.push(sc);
                            self.advance();
                        }
                        continue;
                    }
                    if c == '\'' {
                        // Single-quoted string literal inside expression
                        // e.g., {items.join(', ')}
                        self.advance(); // consume opening '
                        expr.push('\'');
                        while let Some(sc) = self.peek() {
                            if sc == '\'' {
                                expr.push('\'');
                                self.advance();
                                break;
                            }
                            if sc == '\n' || sc == '"' {
                                // Don't consume the f-string delimiter or newline
                                // inside a single-quoted string within an expression.
                                // If we reach '"', the single quote was likely meant
                                // as a literal character, not a string delimiter.
                                break;
                            }
                            expr.push(sc);
                            self.advance();
                        }
                        continue;
                    }
                    if c == '}' {
                        brace_depth -= 1;
                        if brace_depth == 0 {
                            self.advance();
                            break;
                        }
                    } else if c == '{' {
                        brace_depth += 1;
                    } else if c == '\n' {
                        // Expression spans newline -- continue (multi-line f-string expr)
                        self.line += 1;
                        self.column = 0;
                    }
                    expr.push(c);
                    self.advance();
                }
                if brace_depth != 0 {
                    // Could not find closing } -- treat { and expression as literal text
                    current_literal.push('{');
                    current_literal.push_str(&expr);
                    continue;
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
                    // Lone } -- treat as literal } (matching Simple's lenient behavior)
                    current_literal.push('}');
                }
            } else if ch == '\\' {
                self.advance();
                match self.process_escape(true) {
                    EscapeResult::Char(c) => current_literal.push(c),
                    EscapeResult::Chars(chars) => {
                        for c in chars {
                            current_literal.push(c);
                        }
                    }
                    EscapeResult::Error(msg) => return TokenKind::Error(msg),
                    EscapeResult::Unterminated => {
                        return TokenKind::Error("Unterminated f-string".to_string())
                    }
                }
            } else if ch == '\n' {
                // Allow multi-line f-strings (Simple supports this)
                self.advance();
                self.line += 1;
                self.column = 0;
                current_literal.push('\n');
            } else {
                self.advance();
                current_literal.push(ch);
            }
        }

        TokenKind::Error("Unterminated f-string".to_string())
    }

}
