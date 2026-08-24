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
                if ch == '\n' {
                    self.line += 1;
                    self.column = 1;
                }
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
        // Uncollapsed mirror of `current_literal`, kept only so a failed
        // interpolation-expression scan can backtrack to the exact raw text.
        // The documented language contract (regression: doc/08_tracking/bug/
        // runtime_surface_spec_brace_escape_contains_red_2026-08-17.md, pinned
        // by lexer_tests_literals.rs::double_braces_collapse_to_one_literal_brace)
        // is that `{{`/`}}` collapse to a single literal brace in EVERY
        // double-quoted text literal, interpolated or not — a briefly-landed
        // "keep raw when no interpolation" variant broke `.contains()` against
        // single-brace text and was reverted here.
        let mut current_literal_raw = String::new();
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
                        let _ = &current_literal_raw;
                        let literal_text = current_literal;
                        if !literal_text.is_empty() {
                            parts.push(FStringToken::Literal(literal_text));
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
                    // `{{`/`}}` collapse applies uniformly, with or without
                    // interpolation (see comment at `current_literal_raw`).
                    let literal_text = current_literal;
                    if !literal_text.is_empty() {
                        parts.push(FStringToken::Literal(literal_text.clone()));
                    }

                    // Check for unit suffix (only allowed if no interpolation)
                    if !has_interpolation {
                        if let Some(suffix) = self.scan_string_unit_suffix() {
                            // Simple string with unit suffix: "127.0.0.1"_ip
                            return TokenKind::TypedString(literal_text, suffix);
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
                    current_literal_raw.push_str("{{");
                    continue;
                }
                // Check if next char is backslash - this can't be a valid expression start
                // This handles JSON patterns like {\"key\": \"value\"}
                // where { is followed by an escape sequence
                if self.check('\\') {
                    current_literal.push('{');
                    current_literal_raw.push('{');
                    continue;
                }
                // Check if next char is a quote immediately after {
                // This handles patterns like '{' in "expected '{' after 'loss'"
                // where the user wants literal braces in the string
                if self.check('\'') || self.check('"') {
                    current_literal.push('{');
                    current_literal_raw.push('{');
                    continue;
                }
                // Save state for backtracking if expression scanning fails
                let saved_state = self.clone();
                let saved_parts_len = parts.len();
                let saved_literal = current_literal.clone();
                let saved_literal_raw = current_literal_raw.clone();

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
                let mut paren_depth = 0; // Track () and [] nesting for format spec detection
                let mut in_string: Option<char> = None; // Track if inside string and which quote
                let mut expr_failed = false;
                // Track the byte offset of the last top-level ':' for format spec splitting.
                // A top-level ':' means: brace_depth==1, paren_depth==0, not in a string.
                let mut last_top_colon: Option<usize> = None;
                while let Some(c) = self.peek() {
                    // An unescaped newline inside a non-triple f-string's
                    // interpolation expression means the `{` was never
                    // matched on this line (e.g. a literal `{` in a
                    // single-line string). Stop and backtrack so an
                    // unmatched brace cannot run away across lines and
                    // consume later, unrelated source (functions, strings,
                    // etc). Triple f-strings legitimately allow multi-line
                    // expressions and are unaffected.
                    if c == '\n' && !is_triple {
                        expr_failed = true;
                        break;
                    }
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
                    // Track unescaped string boundaries: an unescaped double
                    // quote toggles a nested string literal inside the
                    // interpolation expression (e.g. `{xs.join("-")}`).
                    // Braces/quotes inside that nested string don't affect
                    // interpolation depth. Escaped quotes are handled by the
                    // backslash arm above. Runaway unmatched `{` across lines
                    // is separately contained by the newline guard above.
                    //
                    // A nested string may only OPEN where an operand is
                    // genuinely expected: inside a call/index (`paren_depth >
                    // 0`, e.g. `{xs.join("-")}`), after a binary/logical
                    // operator (`{k != ""}`), or inside an inline conditional
                    // (`{if c: "y" else: "n"}`). Anywhere else at
                    // `paren_depth == 0` the quote closes the OUTER string,
                    // i.e. the `{` was a literal brace -- stop and backtrack,
                    // otherwise the scanner swallows the concatenation
                    // operators of `"p { " + x + " }"` and emits `" + x + "`
                    // verbatim. Triple f-strings keep the permissive form.
                    if c == '"' {
                        if let Some(quote) = in_string {
                            if quote == c {
                                in_string = None; // End of string
                            }
                        } else if paren_depth == 0 && !is_triple && !Self::nested_string_may_open(&expr) {
                            expr_failed = true;
                            break;
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
                                .is_some_and(|last| last.is_alphanumeric() || last == '_' || last == ')');
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
                    // Only track braces/parens when not in a string
                    if in_string.is_none() {
                        if c == '}' {
                            brace_depth -= 1;
                            if brace_depth == 0 {
                                self.advance();
                                break;
                            }
                        } else if c == '{' {
                            brace_depth += 1;
                        } else if c == '(' || c == '[' {
                            paren_depth += 1;
                        } else if c == ')' || c == ']' {
                            if paren_depth > 0 {
                                paren_depth -= 1;
                            }
                        } else if c == ':' && brace_depth == 1 && paren_depth == 0 {
                            // Record position of top-level ':' — could be format spec
                            last_top_colon = Some(expr.len());
                        }
                    }
                    expr.push(c);
                    self.advance();
                }
                // If expression scanning failed or braces unmatched, backtrack
                // and treat the { as a literal character
                if expr_failed || brace_depth != 0 {
                    *self = saved_state;
                    parts.truncate(saved_parts_len);
                    current_literal = saved_literal;
                    current_literal_raw = saved_literal_raw;
                    current_literal.push('{');
                    current_literal_raw.push('{');
                    continue;
                }
                // If expression is empty (just "{}"), treat as literal "{}"
                // This allows strings like "m{} block" without escaping
                if expr.trim().is_empty() {
                    current_literal.push_str("{}");
                    current_literal_raw.push_str("{}");
                } else {
                    // Check if we found a top-level ':' that introduces a format spec.
                    // Format specs follow Python conventions: [fill][align][sign][#][0][width][grouping][.precision][type]
                    // Valid format spec chars: <>=^+- #0123456789.bcdoxXeEfFgGns%
                    // We validate that the part after ':' looks like a format spec to avoid
                    // false positives with dict literals, lambdas, and ternary expressions.
                    if let Some(colon_pos) = last_top_colon {
                        let after_colon = &expr[colon_pos + 1..];
                        if Self::is_format_spec(after_colon) {
                            let expr_part = expr[..colon_pos].to_string();
                            let spec_part = after_colon.to_string();
                            parts.push(FStringToken::ExprWithFormat(expr_part, spec_part));
                            has_interpolation = true;
                        } else {
                            parts.push(FStringToken::Expr(expr));
                            has_interpolation = true;
                        }
                    } else {
                        parts.push(FStringToken::Expr(expr));
                        has_interpolation = true; // Mark that we have interpolation
                    }
                }
            } else if ch == '}' {
                self.advance();
                // Check for escaped }} -> literal }
                if self.check('}') {
                    self.advance();
                    current_literal.push('}');
                    current_literal_raw.push_str("}}");
                } else {
                    // Treat single } as literal } (lenient mode)
                    // This allows strings like "{value}}" to work where the } is part of JSON syntax
                    current_literal.push('}');
                    current_literal_raw.push('}');
                }
            } else if ch == '\\' {
                self.advance();
                match self.process_escape(true) {
                    EscapeResult::Char(c) => {
                        current_literal.push(c);
                        current_literal_raw.push(c);
                    }
                    EscapeResult::Error(msg) => return TokenKind::Error(msg),
                    EscapeResult::Unterminated => return TokenKind::Error("Unterminated f-string".to_string()),
                }
            } else if ch == '\n' {
                if is_triple {
                    // Newlines are allowed in triple-quoted f-strings
                    self.advance();
                    self.line += 1;
                    self.column = 1;
                    current_literal.push(ch);
                    current_literal_raw.push(ch);
                } else {
                    return TokenKind::Error("Unterminated f-string".to_string());
                }
            } else {
                self.advance();
                current_literal.push(ch);
                current_literal_raw.push(ch);
            }
        }

        if is_triple {
            TokenKind::Error("Unterminated triple-quoted f-string".to_string())
        } else {
            TokenKind::Error("Unterminated f-string".to_string())
        }
    }

    /// Check if a string looks like a Python-style format specifier.
    ///
    /// Format spec grammar: [[fill]align][sign][z][#][0][width][grouping_option][.precision][type]
    ///   fill      = any character (if followed by align)
    ///   align     = '<' | '>' | '^' | '='
    ///   sign      = '+' | '-' | ' '
    ///   width     = digit+
    ///   grouping  = '_' | ','
    ///   precision = '.' digit+
    ///   type      = 'b'|'c'|'d'|'e'|'E'|'f'|'F'|'g'|'G'|'n'|'o'|'s'|'x'|'X'|'%'
    ///
    /// We use a heuristic: the spec must be non-empty and consist only of valid
    /// format spec characters — no alphanumeric identifiers, no operators like `=`, etc.
    /// that would indicate this is actually a dict literal or ternary expression.
    /// May an unescaped `"` open a NESTED string here, given the interpolation
    /// expression text scanned so far, at `paren_depth == 0` of a single-line
    /// f-string?
    ///
    /// Only where an operand is genuinely expected. Otherwise the quote is the
    /// OUTER string's closing quote and the `{` was a literal brace -- see bug
    /// `string_literal_brace_breaks_concat_2026-06-29`, where `"p { " + x + " }"`
    /// had its `+` operators swallowed and emitted verbatim.
    fn nested_string_may_open(expr: &str) -> bool {
        fn is_word_byte(b: u8) -> bool {
            b.is_ascii_alphanumeric() || b == b'_'
        }
        fn has_word(text: &str, word: &str) -> bool {
            let bytes = text.as_bytes();
            let mut from = 0;
            while let Some(rel) = text[from..].find(word) {
                let start = from + rel;
                let end = start + word.len();
                let before_ok = start == 0 || !is_word_byte(bytes[start - 1]);
                let after_ok = end == bytes.len() || !is_word_byte(bytes[end]);
                if before_ok && after_ok {
                    return true;
                }
                from = start + 1;
            }
            false
        }

        // Inline conditional / match arms legitimately hold bare string literals.
        if has_word(expr, "if") || has_word(expr, "else") || has_word(expr, "match") {
            return true;
        }
        let trimmed = expr.trim_end();
        if trimmed.is_empty() {
            // `{ "` -- nothing to be an operand OF.
            return false;
        }
        // Binary / logical operator => an operand must follow.
        // Null-coalescing `??` — its RHS is an operand position, so a string
        // literal may legitimately open there (`{x ?? "d"}`).
        for op in ["==", "!=", "<=", ">=", "??"] {
            if trimmed.ends_with(op) {
                return true;
            }
        }
        if trimmed.ends_with(['<', '>', '+', '-', '*', '/', '%', ',', '(', '[']) {
            return true;
        }
        for kw in ["and", "or", "not", "in"] {
            if trimmed.ends_with(kw) {
                let head = &trimmed[..trimmed.len() - kw.len()];
                if head.is_empty() || !Self::is_word_byte(head.as_bytes()[head.len() - 1]) {
                    return true;
                }
            }
        }
        false
    }

    fn is_word_byte(b: u8) -> bool {
        b.is_ascii_alphanumeric() || b == b'_'
    }

    fn is_format_spec(s: &str) -> bool {
        if s.is_empty() {
            return false;
        }

        // Format spec characters (Python-style):
        // Alignment: < > ^ =
        // Sign: + -
        // Fill/prefix: # 0
        // Grouping: , _
        // Precision: .
        // Digits: 0-9
        // Type codes: b c d e E f F g G n o s x X %
        // Space (for sign)
        let valid_chars: &[char] = &[
            '<', '>', '^', '=', '+', '-', ' ', '#', '0', ',', '_', '.', 'b', 'c', 'd', 'e', 'E', 'f', 'F', 'g', 'G',
            'n', 'o', 's', 'x', 'X', '%', '1', '2', '3', '4', '5', '6', '7', '8', '9',
        ];

        // First character can be a fill character (any char) if second is an alignment char
        let chars: Vec<char> = s.chars().collect();

        // If the spec starts with a fill+align pair, skip the fill char for validation
        let start = if chars.len() >= 2 && matches!(chars[1], '<' | '>' | '^' | '=') {
            // First char is fill, second is align — skip the fill char
            // Fill char can be anything
            2
        } else {
            0
        };

        // All remaining characters must be valid format spec characters
        for &ch in &chars[start..] {
            if !valid_chars.contains(&ch) {
                return false;
            }
        }

        true
    }
}
