//! SUI token types for template lexing

use std::fmt;

/// Source location for error reporting
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

impl Span {
    pub fn new(start: usize, end: usize, line: usize, column: usize) -> Self {
        Self {
            start,
            end,
            line,
            column,
        }
    }

    pub fn merge(&self, other: &Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
            line: self.line,
            column: self.column,
        }
    }
}

impl Default for Span {
    fn default() -> Self {
        Self {
            start: 0,
            end: 0,
            line: 1,
            column: 1,
        }
    }
}

/// A token with its kind, span, and lexeme
#[derive(Debug, Clone, PartialEq)]
pub struct SuiToken {
    pub kind: SuiTokenKind,
    pub span: Span,
    pub lexeme: String,
}

impl SuiToken {
    pub fn new(kind: SuiTokenKind, span: Span, lexeme: String) -> Self {
        Self { kind, span, lexeme }
    }
}

/// Token types for SUI templates
#[derive(Debug, Clone, PartialEq)]
pub enum SuiTokenKind {
    // Template block delimiters
    DirectiveOpen,  // {@
    DirectiveClose, // @}
    DeclOpen,       // {$
    DeclClose,      // $}
    ServerOpen,     // {-
    ServerClose,    // -}
    ClientOpen,     // {+
    ClientClose,    // +}
    OutputOpen,     // {{
    OutputClose,    // }}
    RawOutputOpen,  // {!
    RawOutputClose, // !}
    ControlOpen,    // {%
    ControlClose,   // %}
    CommentOpen,    // {#
    CommentClose,   // #}

    // HTML tokens
    TagOpen,      // <
    TagClose,     // >
    TagSelfClose, // />
    TagEndOpen,   // </

    // Literals
    Text(String),
    Identifier(String),
    String(String),
    Integer(i64),
    Float(f64),
    Bool(bool),

    // Operators
    Assign,    // =
    Eq,        // ==
    NotEq,     // !=
    Lt,        // <
    Gt,        // >
    LtEq,      // <=
    GtEq,      // >=
    Plus,      // +
    Minus,     // -
    Star,      // *
    Slash,     // /
    Percent,   // %
    And,       // and, &&
    Or,        // or, ||
    Not,       // not, !
    Dot,       // .
    DoubleDot, // ..

    // Punctuation
    Colon,     // :
    Comma,     // ,
    Semicolon, // ;
    LParen,    // (
    RParen,    // )
    LBracket,  // [
    RBracket,  // ]
    LBrace,    // {
    RBrace,    // }
    Pipe,      // |
    Arrow,     // =>

    // Control keywords (inside {% %})
    If,
    Elif,
    Else,
    End,
    For,
    In,
    Let,
    While,
    Break,
    Continue,

    // Directive keywords (inside {@ @})
    Component,
    Page,
    Layout,
    Embed,
    Slot,
    Fill,
    Hydrate,

    // Special
    Newline,
    Whitespace,
    Comment(String),
    Eof,
    Error(String),
}

impl SuiTokenKind {
    /// Check if this is a template block opener
    pub fn is_block_open(&self) -> bool {
        matches!(
            self,
            SuiTokenKind::DirectiveOpen
                | SuiTokenKind::DeclOpen
                | SuiTokenKind::ServerOpen
                | SuiTokenKind::ClientOpen
                | SuiTokenKind::OutputOpen
                | SuiTokenKind::RawOutputOpen
                | SuiTokenKind::ControlOpen
                | SuiTokenKind::CommentOpen
        )
    }

    /// Check if this is a template block closer
    pub fn is_block_close(&self) -> bool {
        matches!(
            self,
            SuiTokenKind::DirectiveClose
                | SuiTokenKind::DeclClose
                | SuiTokenKind::ServerClose
                | SuiTokenKind::ClientClose
                | SuiTokenKind::OutputClose
                | SuiTokenKind::RawOutputClose
                | SuiTokenKind::ControlClose
                | SuiTokenKind::CommentClose
        )
    }

    /// Get keyword from identifier string
    pub fn keyword_from_str(s: &str) -> Option<SuiTokenKind> {
        match s {
            // Control keywords
            "if" => Some(SuiTokenKind::If),
            "elif" => Some(SuiTokenKind::Elif),
            "else" => Some(SuiTokenKind::Else),
            "end" => Some(SuiTokenKind::End),
            "for" => Some(SuiTokenKind::For),
            "in" => Some(SuiTokenKind::In),
            "let" => Some(SuiTokenKind::Let),
            "while" => Some(SuiTokenKind::While),
            "break" => Some(SuiTokenKind::Break),
            "continue" => Some(SuiTokenKind::Continue),
            // Directive keywords
            "component" => Some(SuiTokenKind::Component),
            "page" => Some(SuiTokenKind::Page),
            "layout" => Some(SuiTokenKind::Layout),
            "embed" => Some(SuiTokenKind::Embed),
            "slot" => Some(SuiTokenKind::Slot),
            "fill" => Some(SuiTokenKind::Fill),
            "hydrate" => Some(SuiTokenKind::Hydrate),
            // Logical operators
            "and" => Some(SuiTokenKind::And),
            "or" => Some(SuiTokenKind::Or),
            "not" => Some(SuiTokenKind::Not),
            // Boolean literals
            "true" => Some(SuiTokenKind::Bool(true)),
            "false" => Some(SuiTokenKind::Bool(false)),
            _ => None,
        }
    }
}

impl fmt::Display for SuiTokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SuiTokenKind::DirectiveOpen => write!(f, "{{@"),
            SuiTokenKind::DirectiveClose => write!(f, "@}}"),
            SuiTokenKind::DeclOpen => write!(f, "{{$"),
            SuiTokenKind::DeclClose => write!(f, "$}}"),
            SuiTokenKind::ServerOpen => write!(f, "{{-"),
            SuiTokenKind::ServerClose => write!(f, "-}}"),
            SuiTokenKind::ClientOpen => write!(f, "{{+"),
            SuiTokenKind::ClientClose => write!(f, "+}}"),
            SuiTokenKind::OutputOpen => write!(f, "{{{{"),
            SuiTokenKind::OutputClose => write!(f, "}}}}"),
            SuiTokenKind::RawOutputOpen => write!(f, "{{!"),
            SuiTokenKind::RawOutputClose => write!(f, "!}}"),
            SuiTokenKind::ControlOpen => write!(f, "{{%"),
            SuiTokenKind::ControlClose => write!(f, "%}}"),
            SuiTokenKind::CommentOpen => write!(f, "{{#"),
            SuiTokenKind::CommentClose => write!(f, "#}}"),
            SuiTokenKind::TagOpen => write!(f, "<"),
            SuiTokenKind::TagClose => write!(f, ">"),
            SuiTokenKind::TagSelfClose => write!(f, "/>"),
            SuiTokenKind::TagEndOpen => write!(f, "</"),
            SuiTokenKind::Text(s) => write!(f, "text({:?})", s),
            SuiTokenKind::Identifier(s) => write!(f, "ident({:?})", s),
            SuiTokenKind::String(s) => write!(f, "string({:?})", s),
            SuiTokenKind::Integer(n) => write!(f, "int({})", n),
            SuiTokenKind::Float(n) => write!(f, "float({})", n),
            SuiTokenKind::Bool(b) => write!(f, "bool({})", b),
            SuiTokenKind::Assign => write!(f, "="),
            SuiTokenKind::Eq => write!(f, "=="),
            SuiTokenKind::NotEq => write!(f, "!="),
            SuiTokenKind::Lt => write!(f, "<"),
            SuiTokenKind::Gt => write!(f, ">"),
            SuiTokenKind::LtEq => write!(f, "<="),
            SuiTokenKind::GtEq => write!(f, ">="),
            SuiTokenKind::Plus => write!(f, "+"),
            SuiTokenKind::Minus => write!(f, "-"),
            SuiTokenKind::Star => write!(f, "*"),
            SuiTokenKind::Slash => write!(f, "/"),
            SuiTokenKind::Percent => write!(f, "%"),
            SuiTokenKind::And => write!(f, "and"),
            SuiTokenKind::Or => write!(f, "or"),
            SuiTokenKind::Not => write!(f, "not"),
            SuiTokenKind::Dot => write!(f, "."),
            SuiTokenKind::DoubleDot => write!(f, ".."),
            SuiTokenKind::Colon => write!(f, ":"),
            SuiTokenKind::Comma => write!(f, ","),
            SuiTokenKind::Semicolon => write!(f, ";"),
            SuiTokenKind::LParen => write!(f, "("),
            SuiTokenKind::RParen => write!(f, ")"),
            SuiTokenKind::LBracket => write!(f, "["),
            SuiTokenKind::RBracket => write!(f, "]"),
            SuiTokenKind::LBrace => write!(f, "{{"),
            SuiTokenKind::RBrace => write!(f, "}}"),
            SuiTokenKind::Pipe => write!(f, "|"),
            SuiTokenKind::Arrow => write!(f, "=>"),
            SuiTokenKind::If => write!(f, "if"),
            SuiTokenKind::Elif => write!(f, "elif"),
            SuiTokenKind::Else => write!(f, "else"),
            SuiTokenKind::End => write!(f, "end"),
            SuiTokenKind::For => write!(f, "for"),
            SuiTokenKind::In => write!(f, "in"),
            SuiTokenKind::Let => write!(f, "let"),
            SuiTokenKind::While => write!(f, "while"),
            SuiTokenKind::Break => write!(f, "break"),
            SuiTokenKind::Continue => write!(f, "continue"),
            SuiTokenKind::Component => write!(f, "component"),
            SuiTokenKind::Page => write!(f, "page"),
            SuiTokenKind::Layout => write!(f, "layout"),
            SuiTokenKind::Embed => write!(f, "embed"),
            SuiTokenKind::Slot => write!(f, "slot"),
            SuiTokenKind::Fill => write!(f, "fill"),
            SuiTokenKind::Hydrate => write!(f, "hydrate"),
            SuiTokenKind::Newline => write!(f, "newline"),
            SuiTokenKind::Whitespace => write!(f, "whitespace"),
            SuiTokenKind::Comment(s) => write!(f, "comment({:?})", s),
            SuiTokenKind::Eof => write!(f, "EOF"),
            SuiTokenKind::Error(s) => write!(f, "error({:?})", s),
        }
    }
}
