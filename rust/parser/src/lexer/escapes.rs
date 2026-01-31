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
}
