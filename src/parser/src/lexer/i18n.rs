//! i18n string lexing support
//!
//! Supports:
//! - Named strings: `Name_"text"` -> I18nString
//! - Template strings: `Name_"Hello {user}!"` -> I18nFString
//! - Triple-quoted: `Name_"""multiline text"""` -> I18nString/I18nFString

use super::escapes::EscapeResult;
use crate::token::{FStringToken, TokenKind};

impl<'a> super::Lexer<'a> {
    /// Scan an i18n string: Name_"text" or Name_"text with {var}"
    /// The name (including trailing underscore) has already been collected.
    /// The opening " has already been consumed.
    pub(super) fn scan_i18n_string(&mut self, name: String) -> TokenKind {
        let mut parts: Vec<FStringToken> = Vec::new();
        let mut current_literal = String::new();
        let mut has_interpolation = false;

        while let Some(ch) = self.peek() {
            match ch {
                '"' => {
                    // End of string
                    self.advance();
                    if !current_literal.is_empty() {
                        parts.push(FStringToken::Literal(current_literal.clone()));
                    }

                    // Return appropriate token type
                    if has_interpolation {
                        return TokenKind::I18nFString { name, parts };
                    } else {
                        // Simple i18n string without interpolation
                        let default_text = parts
                            .into_iter()
                            .map(|p| match p {
                                FStringToken::Literal(s) => s,
                                FStringToken::Expr(_) => unreachable!(),
                            })
                            .collect::<String>();
                        return TokenKind::I18nString { name, default_text };
                    }
                }
                '{' => {
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
                        return TokenKind::Error("Unclosed { in i18n string".to_string());
                    }
                    parts.push(FStringToken::Expr(expr));
                    has_interpolation = true;
                }
                '}' => {
                    self.advance();
                    // Check for escaped }} -> literal }
                    if self.check('}') {
                        self.advance();
                        current_literal.push('}');
                    } else {
                        return TokenKind::Error("Single } in i18n string (use }} to escape)".to_string());
                    }
                }
                '\\' => {
                    self.advance();
                    match self.process_escape(true) {
                        EscapeResult::Char(c) => current_literal.push(c),
                        EscapeResult::Error(msg) => return TokenKind::Error(msg),
                        EscapeResult::Unterminated => return TokenKind::Error("Unterminated i18n string".to_string()),
                    }
                }
                '\n' => {
                    // Newlines not allowed in single-line i18n strings
                    return TokenKind::Error("Unterminated i18n string".to_string());
                }
                _ => {
                    self.advance();
                    current_literal.push(ch);
                }
            }
        }

        TokenKind::Error("Unterminated i18n string".to_string())
    }

    /// Scan a triple-quoted i18n string: Name_"""text""" or Name_"""text with {var}"""
    /// The name (including trailing underscore) has already been collected.
    /// The first opening " has already been consumed.
    pub(super) fn scan_i18n_triple_string(&mut self, name: String) -> TokenKind {
        // Consume the two remaining opening quotes
        self.advance(); // Second "
        self.advance(); // Third "

        let mut parts: Vec<FStringToken> = Vec::new();
        let mut current_literal = String::new();
        let mut has_interpolation = false;

        while let Some(ch) = self.peek() {
            match ch {
                '"' => {
                    // Check for closing """
                    if self.peek_ahead(1) == Some('"') && self.peek_ahead(2) == Some('"') {
                        // Found closing """
                        self.advance(); // First "
                        self.advance(); // Second "
                        self.advance(); // Third "

                        if !current_literal.is_empty() {
                            parts.push(FStringToken::Literal(current_literal.clone()));
                        }

                        // Return appropriate token type
                        if has_interpolation {
                            return TokenKind::I18nFString { name, parts };
                        } else {
                            // Simple i18n string without interpolation
                            let default_text = parts
                                .into_iter()
                                .map(|p| match p {
                                    FStringToken::Literal(s) => s,
                                    FStringToken::Expr(_) => unreachable!(),
                                })
                                .collect::<String>();
                            return TokenKind::I18nString { name, default_text };
                        }
                    } else {
                        // Single " inside the string - treat as literal
                        self.advance();
                        current_literal.push('"');
                    }
                }
                '{' => {
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
                        return TokenKind::Error("Unclosed { in i18n string".to_string());
                    }
                    parts.push(FStringToken::Expr(expr));
                    has_interpolation = true;
                }
                '}' => {
                    self.advance();
                    // Check for escaped }} -> literal }
                    if self.check('}') {
                        self.advance();
                        current_literal.push('}');
                    } else {
                        return TokenKind::Error("Single } in i18n string (use }} to escape)".to_string());
                    }
                }
                '\\' => {
                    self.advance();
                    match self.process_escape(true) {
                        EscapeResult::Char(c) => current_literal.push(c),
                        EscapeResult::Error(msg) => return TokenKind::Error(msg),
                        EscapeResult::Unterminated => {
                            return TokenKind::Error("Unterminated triple-quoted i18n string".to_string())
                        }
                    }
                }
                '\n' => {
                    // Newlines are allowed in triple-quoted strings
                    self.advance();
                    self.line += 1;
                    self.column = 1;
                    current_literal.push(ch);
                }
                _ => {
                    self.advance();
                    current_literal.push(ch);
                }
            }
        }

        TokenKind::Error("Unterminated triple-quoted i18n string".to_string())
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::Lexer;
    use crate::token::TokenKind;

    #[test]
    fn test_i18n_string_simple() {
        let mut lexer = Lexer::new(r#"Login_failed_"Login failed""#);
        let tokens = lexer.tokenize();
        assert!(matches!(
            &tokens[0].kind,
            TokenKind::I18nString { name, default_text }
            if name == "Login_failed_" && default_text == "Login failed"
        ));
    }

    #[test]
    fn test_i18n_fstring_with_interpolation() {
        let mut lexer = Lexer::new(r#"Welcome_"Hello {name}!""#);
        let tokens = lexer.tokenize();
        assert!(matches!(
            &tokens[0].kind,
            TokenKind::I18nFString { name, parts }
            if name == "Welcome_" && parts.len() == 3
        ));
    }

    #[test]
    fn test_i18n_triple_quoted() {
        let mut lexer = Lexer::new(
            r#"Desc_"""This is a
multiline description.""""#,
        );
        let tokens = lexer.tokenize();
        assert!(matches!(
            &tokens[0].kind,
            TokenKind::I18nString { name, default_text }
            if name == "Desc_" && default_text.contains('\n')
        ));
    }
}
