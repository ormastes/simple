/// Source location
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

impl Span {
    pub fn new(start: usize, end: usize, line: usize, column: usize) -> Self {
        Self { start, end, line, column }
    }
}

/// Token types for the Simple language
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    Integer(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Nil,
    Symbol(String),      // :symbol

    // Identifiers and Keywords
    Identifier(String),

    // Keywords
    Fn,
    Let,
    Mut,
    If,
    Elif,
    Else,
    For,
    While,
    Loop,
    Break,
    Continue,
    Return,
    Match,
    Struct,
    Class,
    Enum,
    Trait,
    Impl,
    Actor,
    Pub,
    Priv,
    Import,
    From,
    As,
    In,
    Is,
    Not,
    And,
    Or,
    True,
    False,
    Spawn,
    New,
    Self_,
    Super,
    Async,
    Await,
    Waitless,

    // Operators
    Plus,           // +
    Minus,          // -
    Star,           // *
    Slash,          // /
    Percent,        // %
    DoubleStar,     // **
    DoubleSlash,    // //

    Eq,             // ==
    NotEq,          // !=
    Lt,             // <
    Gt,             // >
    LtEq,           // <=
    GtEq,           // >=

    Assign,         // =
    PlusAssign,     // +=
    MinusAssign,    // -=
    StarAssign,     // *=
    SlashAssign,    // /=

    Ampersand,      // &
    Pipe,           // |
    Caret,          // ^
    Tilde,          // ~
    ShiftLeft,      // <<
    ShiftRight,     // >>

    Arrow,          // ->
    FatArrow,       // =>

    // Delimiters
    LParen,         // (
    RParen,         // )
    LBracket,       // [
    RBracket,       // ]
    LBrace,         // {
    RBrace,         // }

    Comma,          // ,
    Colon,          // :
    DoubleColon,    // ::
    Semicolon,      // ;
    Dot,            // .
    DoubleDot,      // ..
    Ellipsis,       // ...
    Question,       // ?
    At,             // @
    Hash,           // #
    Dollar,         // $
    Backslash,      // \
    Underscore,     // _ (as pattern)

    // Indentation tokens
    Newline,
    Indent,
    Dedent,

    // Special
    Eof,
    Error(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub lexeme: String,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span, lexeme: String) -> Self {
        Self { kind, span, lexeme }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_creation() {
        let span = Span::new(0, 5, 1, 1);
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 5);
        assert_eq!(span.line, 1);
        assert_eq!(span.column, 1);
    }

    #[test]
    fn test_token_creation() {
        let token = Token::new(
            TokenKind::Integer(42),
            Span::new(0, 2, 1, 1),
            "42".to_string(),
        );
        assert_eq!(token.kind, TokenKind::Integer(42));
        assert_eq!(token.lexeme, "42");
    }
}
