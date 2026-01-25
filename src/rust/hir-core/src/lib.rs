//! Simple HIR Core - Shared types for compiler and interpreter
//!
//! This crate provides shared data layout types used by both the
//! tree-walking interpreter and the compiled code runtime.
//!
//! # Layout Types
//!
//! - `StructLayout` - Layout information for struct types
//! - `EnumLayout` - Layout information for enum types (tagged unions)
//! - `FieldLayout` - Layout information for individual fields
//!
//! # Log Levels
//!
//! Log levels 0-10 for unified logging:
//! - 0 = Off
//! - 1 = Fatal
//! - 2 = Error
//! - 3 = Warn
//! - 4 = Info
//! - 5 = Debug
//! - 6 = Trace
//! - 7 = Verbose
//! - 10 = All

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

//==============================================================================
// Log Levels (0-10)
//==============================================================================

/// Log level constants
pub mod log_level {
    pub const OFF: u8 = 0;
    pub const FATAL: u8 = 1;
    pub const ERROR: u8 = 2;
    pub const WARN: u8 = 3;
    pub const INFO: u8 = 4;
    pub const DEBUG: u8 = 5;
    pub const TRACE: u8 = 6;
    pub const VERBOSE: u8 = 7;
    pub const ALL: u8 = 10;
}

/// Log level enum
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[repr(u8)]
pub enum LogLevel {
    Off = 0,
    Fatal = 1,
    Error = 2,
    Warn = 3,
    Info = 4,
    Debug = 5,
    Trace = 6,
    Verbose = 7,
    All = 10,
}

impl LogLevel {
    pub fn from_u8(level: u8) -> Self {
        match level {
            0 => LogLevel::Off,
            1 => LogLevel::Fatal,
            2 => LogLevel::Error,
            3 => LogLevel::Warn,
            4 => LogLevel::Info,
            5 => LogLevel::Debug,
            6 => LogLevel::Trace,
            7 => LogLevel::Verbose,
            8..=10 => LogLevel::All,
            _ => LogLevel::Info,
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            LogLevel::Off => "off",
            LogLevel::Fatal => "fatal",
            LogLevel::Error => "error",
            LogLevel::Warn => "warn",
            LogLevel::Info => "info",
            LogLevel::Debug => "debug",
            LogLevel::Trace => "trace",
            LogLevel::Verbose => "verbose",
            LogLevel::All => "all",
        }
    }
}

impl Default for LogLevel {
    fn default() -> Self {
        LogLevel::Info
    }
}

//==============================================================================
// Type Kinds
//==============================================================================

/// Primitive type kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PrimitiveKind {
    Bool,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Char,
    Unit,
}

impl PrimitiveKind {
    /// Get the size in bytes
    pub fn size(&self) -> usize {
        match self {
            PrimitiveKind::Bool => 1,
            PrimitiveKind::I8 | PrimitiveKind::U8 => 1,
            PrimitiveKind::I16 | PrimitiveKind::U16 => 2,
            PrimitiveKind::I32 | PrimitiveKind::U32 | PrimitiveKind::F32 => 4,
            PrimitiveKind::I64 | PrimitiveKind::U64 | PrimitiveKind::F64 => 8,
            PrimitiveKind::Char => 4,
            PrimitiveKind::Unit => 0,
        }
    }

    /// Get the alignment in bytes
    pub fn align(&self) -> usize {
        self.size().max(1)
    }
}

//==============================================================================
// Field Layout
//==============================================================================

/// Layout information for a field within a struct or enum variant
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldLayout {
    /// Field name
    pub name: String,
    /// Offset from start of struct (bytes)
    pub offset: usize,
    /// Size in bytes
    pub size: usize,
    /// Alignment requirement
    pub align: usize,
    /// Type name (for debugging)
    pub type_name: String,
}

impl FieldLayout {
    pub fn new(name: impl Into<String>, offset: usize, size: usize, align: usize) -> Self {
        Self {
            name: name.into(),
            offset,
            size,
            align,
            type_name: String::new(),
        }
    }

    pub fn with_type(mut self, type_name: impl Into<String>) -> Self {
        self.type_name = type_name.into();
        self
    }
}

//==============================================================================
// Struct Layout
//==============================================================================

/// Layout information for a struct type
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructLayout {
    /// Type name
    pub name: String,
    /// Total size in bytes
    pub size: usize,
    /// Alignment requirement
    pub align: usize,
    /// Field layouts in order
    pub fields: Vec<FieldLayout>,
    /// Field name to index mapping
    pub field_indices: HashMap<String, usize>,
}

impl StructLayout {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            size: 0,
            align: 1,
            fields: Vec::new(),
            field_indices: HashMap::new(),
        }
    }

    /// Add a field and compute layout
    pub fn add_field(&mut self, name: impl Into<String>, size: usize, align: usize) {
        let name = name.into();

        // Align the offset
        let offset = (self.size + align - 1) & !(align - 1);

        let field = FieldLayout::new(&name, offset, size, align);
        self.field_indices.insert(name, self.fields.len());
        self.fields.push(field);

        // Update struct size and alignment
        self.size = offset + size;
        self.align = self.align.max(align);
    }

    /// Finalize layout (add padding at end)
    pub fn finalize(&mut self) {
        // Align total size to struct alignment
        self.size = (self.size + self.align - 1) & !(self.align - 1);
    }

    /// Get field index by name
    pub fn field_index(&self, name: &str) -> Option<usize> {
        self.field_indices.get(name).copied()
    }

    /// Get field by name
    pub fn field(&self, name: &str) -> Option<&FieldLayout> {
        self.field_index(name).map(|i| &self.fields[i])
    }
}

//==============================================================================
// Enum Layout
//==============================================================================

/// Layout information for an enum variant
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VariantLayout {
    /// Variant name
    pub name: String,
    /// Discriminant value (tag)
    pub discriminant: u64,
    /// Payload fields (if any)
    pub fields: Vec<FieldLayout>,
    /// Total payload size
    pub payload_size: usize,
}

impl VariantLayout {
    pub fn new(name: impl Into<String>, discriminant: u64) -> Self {
        Self {
            name: name.into(),
            discriminant,
            fields: Vec::new(),
            payload_size: 0,
        }
    }

    pub fn unit(name: impl Into<String>, discriminant: u64) -> Self {
        Self::new(name, discriminant)
    }

    pub fn with_payload(
        name: impl Into<String>,
        discriminant: u64,
        fields: Vec<FieldLayout>,
    ) -> Self {
        let payload_size = fields.iter().map(|f| f.offset + f.size).max().unwrap_or(0);
        Self {
            name: name.into(),
            discriminant,
            fields,
            payload_size,
        }
    }
}

/// Layout information for an enum type (tagged union)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnumLayout {
    /// Type name
    pub name: String,
    /// Size of discriminant (tag) in bytes
    pub tag_size: usize,
    /// Maximum payload size across all variants
    pub max_payload_size: usize,
    /// Total size (tag + max payload)
    pub size: usize,
    /// Alignment requirement
    pub align: usize,
    /// Variant layouts
    pub variants: Vec<VariantLayout>,
    /// Variant name to index mapping
    pub variant_indices: HashMap<String, usize>,
}

impl EnumLayout {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            tag_size: 1, // Default to u8 tag
            max_payload_size: 0,
            size: 0,
            align: 1,
            variants: Vec::new(),
            variant_indices: HashMap::new(),
        }
    }

    /// Add a variant
    pub fn add_variant(&mut self, variant: VariantLayout) {
        self.variant_indices
            .insert(variant.name.clone(), self.variants.len());
        self.max_payload_size = self.max_payload_size.max(variant.payload_size);
        self.variants.push(variant);

        // Update tag size based on variant count
        let count = self.variants.len();
        if count > 256 {
            self.tag_size = 2;
        }
        if count > 65536 {
            self.tag_size = 4;
        }
    }

    /// Finalize layout
    pub fn finalize(&mut self) {
        // Tag alignment
        let tag_align = self.tag_size;

        // Find max payload alignment
        let payload_align = self
            .variants
            .iter()
            .flat_map(|v| v.fields.iter())
            .map(|f| f.align)
            .max()
            .unwrap_or(1);

        self.align = tag_align.max(payload_align);

        // Payload starts after tag, aligned
        let payload_offset = (self.tag_size + payload_align - 1) & !(payload_align - 1);
        self.size = payload_offset + self.max_payload_size;

        // Align total size
        self.size = (self.size + self.align - 1) & !(self.align - 1);
    }

    /// Get variant by name
    pub fn variant(&self, name: &str) -> Option<&VariantLayout> {
        self.variant_indices.get(name).map(|&i| &self.variants[i])
    }

    /// Get discriminant for variant name
    pub fn discriminant(&self, name: &str) -> Option<u64> {
        self.variant(name).map(|v| v.discriminant)
    }
}

//==============================================================================
// Token Categories (for syntax highlighting)
//==============================================================================

/// Token category for syntax highlighting.
/// Used by TreeSitter, LSP, and other tools.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TokenCategory {
    /// Keywords: fn, val, var, if, else, for, while, etc.
    Keyword,
    /// Control flow: if, else, match, for, while, break, continue, return
    ControlFlow,
    /// Type keywords: struct, class, enum, trait, impl
    TypeKeyword,
    /// Operators: +, -, *, /, ==, !=, etc.
    Operator,
    /// Delimiters: (, ), {, }, [, ]
    Delimiter,
    /// Punctuation: ,, :, ;, ., ->
    Punctuation,
    /// Integer literals: 42, 0xFF, 0b1010
    IntegerLiteral,
    /// Float literals: 3.14, 1e-5
    FloatLiteral,
    /// String literals: "hello", 'raw'
    StringLiteral,
    /// Boolean literals: true, false
    BoolLiteral,
    /// Null/nil literals
    NullLiteral,
    /// Identifiers (variables, functions)
    Identifier,
    /// Type names (PascalCase)
    TypeName,
    /// Constants (ALL_CAPS)
    Constant,
    /// Comments: # line, /** block */
    Comment,
    /// Doc comments: ## or /** */
    DocComment,
    /// Whitespace and indentation
    Whitespace,
    /// Newline
    Newline,
    /// Error token
    Error,
    /// End of file
    Eof,
}

impl TokenCategory {
    /// Get the CSS class name for syntax highlighting
    pub fn css_class(&self) -> &'static str {
        match self {
            TokenCategory::Keyword => "keyword",
            TokenCategory::ControlFlow => "control",
            TokenCategory::TypeKeyword => "type-keyword",
            TokenCategory::Operator => "operator",
            TokenCategory::Delimiter => "delimiter",
            TokenCategory::Punctuation => "punctuation",
            TokenCategory::IntegerLiteral => "number",
            TokenCategory::FloatLiteral => "number",
            TokenCategory::StringLiteral => "string",
            TokenCategory::BoolLiteral => "boolean",
            TokenCategory::NullLiteral => "null",
            TokenCategory::Identifier => "identifier",
            TokenCategory::TypeName => "type",
            TokenCategory::Constant => "constant",
            TokenCategory::Comment => "comment",
            TokenCategory::DocComment => "doc-comment",
            TokenCategory::Whitespace => "whitespace",
            TokenCategory::Newline => "newline",
            TokenCategory::Error => "error",
            TokenCategory::Eof => "eof",
        }
    }

    /// Get the TreeSitter scope name
    pub fn treesitter_scope(&self) -> &'static str {
        match self {
            TokenCategory::Keyword => "keyword",
            TokenCategory::ControlFlow => "keyword.control",
            TokenCategory::TypeKeyword => "keyword.type",
            TokenCategory::Operator => "operator",
            TokenCategory::Delimiter => "punctuation.bracket",
            TokenCategory::Punctuation => "punctuation",
            TokenCategory::IntegerLiteral => "constant.numeric.integer",
            TokenCategory::FloatLiteral => "constant.numeric.float",
            TokenCategory::StringLiteral => "string",
            TokenCategory::BoolLiteral => "constant.language.boolean",
            TokenCategory::NullLiteral => "constant.language.null",
            TokenCategory::Identifier => "variable",
            TokenCategory::TypeName => "type",
            TokenCategory::Constant => "constant",
            TokenCategory::Comment => "comment",
            TokenCategory::DocComment => "comment.documentation",
            TokenCategory::Whitespace => "text.whitespace",
            TokenCategory::Newline => "text.whitespace",
            TokenCategory::Error => "invalid",
            TokenCategory::Eof => "text",
        }
    }
}

//==============================================================================
// Base Token Kind (shared by parser and SDN)
//==============================================================================

/// Base token kinds shared by parser, SDN, and TreeSitter.
/// This enum contains the common tokens without payload data.
/// Parser and SDN have their own extended enums with full payloads.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BaseTokenKind {
    // Literals (without payload - use category for highlighting)
    Integer,
    Float,
    String,
    Bool,
    Null,

    // Identifiers
    Identifier,

    // Common keywords (shared by parser and SDN)
    KwTrue,
    KwFalse,
    KwNull,

    // Variable declarations
    KwVal,
    KwVar,
    KwLet,
    KwMut,
    KwConst,

    // Function declarations
    KwFn,
    KwReturn,

    // Control flow
    KwIf,
    KwElse,
    KwElif,
    KwFor,
    KwWhile,
    KwLoop,
    KwBreak,
    KwContinue,
    KwMatch,
    KwCase,

    // Type declarations
    KwStruct,
    KwClass,
    KwEnum,
    KwTrait,
    KwImpl,
    KwType,

    // Visibility
    KwPub,
    KwPriv,

    // Modules
    KwImport,
    KwExport,
    KwFrom,
    KwAs,
    KwMod,
    KwUse,

    // Logic
    KwAnd,
    KwOr,
    KwNot,
    KwIn,
    KwIs,

    // Async
    KwAsync,
    KwAwait,
    KwYield,

    // Other common keywords
    KwSelf,
    KwSuper,
    KwNew,

    // Arithmetic operators
    Plus,       // +
    Minus,      // -
    Star,       // *
    Slash,      // /
    Percent,    // %
    DoubleStar, // **

    // Comparison operators
    Eq,    // ==
    NotEq, // !=
    Lt,    // <
    Gt,    // >
    LtEq,  // <=
    GtEq,  // >=

    // Assignment
    Assign,      // =
    PlusAssign,  // +=
    MinusAssign, // -=
    StarAssign,  // *=
    SlashAssign, // /=

    // Logical operators
    Ampersand,  // &
    Pipe,       // |
    DoubleAmp,  // &&
    DoublePipe, // ||
    Caret,      // ^
    Tilde,      // ~

    // Arrows
    Arrow,    // ->
    FatArrow, // =>

    // Delimiters
    LParen,   // (
    RParen,   // )
    LBracket, // [
    RBracket, // ]
    LBrace,   // {
    RBrace,   // }

    // Punctuation
    Comma,          // ,
    Colon,          // :
    DoubleColon,    // ::
    Semicolon,      // ;
    Dot,            // .
    DoubleDot,      // ..
    DoubleDotEq,    // ..=
    Ellipsis,       // ...
    Question,       // ?
    DoubleQuestion, // ??
    QuestionDot,    // ?.
    At,             // @
    Hash,           // #
    Dollar,         // $
    Backslash,      // \
    Underscore,     // _

    // Whitespace
    Newline,
    Indent,
    Dedent,

    // Comments
    Comment,
    DocComment,

    // Special
    Eof,
    Error,
}

impl BaseTokenKind {
    /// Get the token category for syntax highlighting
    pub fn category(&self) -> TokenCategory {
        match self {
            // Literals
            BaseTokenKind::Integer => TokenCategory::IntegerLiteral,
            BaseTokenKind::Float => TokenCategory::FloatLiteral,
            BaseTokenKind::String => TokenCategory::StringLiteral,
            BaseTokenKind::Bool | BaseTokenKind::KwTrue | BaseTokenKind::KwFalse => {
                TokenCategory::BoolLiteral
            }
            BaseTokenKind::Null | BaseTokenKind::KwNull => TokenCategory::NullLiteral,

            // Identifiers
            BaseTokenKind::Identifier => TokenCategory::Identifier,

            // Control flow keywords
            BaseTokenKind::KwIf
            | BaseTokenKind::KwElse
            | BaseTokenKind::KwElif
            | BaseTokenKind::KwFor
            | BaseTokenKind::KwWhile
            | BaseTokenKind::KwLoop
            | BaseTokenKind::KwBreak
            | BaseTokenKind::KwContinue
            | BaseTokenKind::KwMatch
            | BaseTokenKind::KwCase
            | BaseTokenKind::KwReturn => TokenCategory::ControlFlow,

            // Type keywords
            BaseTokenKind::KwStruct
            | BaseTokenKind::KwClass
            | BaseTokenKind::KwEnum
            | BaseTokenKind::KwTrait
            | BaseTokenKind::KwImpl
            | BaseTokenKind::KwType => TokenCategory::TypeKeyword,

            // Other keywords
            BaseTokenKind::KwVal
            | BaseTokenKind::KwVar
            | BaseTokenKind::KwLet
            | BaseTokenKind::KwMut
            | BaseTokenKind::KwConst
            | BaseTokenKind::KwFn
            | BaseTokenKind::KwPub
            | BaseTokenKind::KwPriv
            | BaseTokenKind::KwImport
            | BaseTokenKind::KwExport
            | BaseTokenKind::KwFrom
            | BaseTokenKind::KwAs
            | BaseTokenKind::KwMod
            | BaseTokenKind::KwUse
            | BaseTokenKind::KwAnd
            | BaseTokenKind::KwOr
            | BaseTokenKind::KwNot
            | BaseTokenKind::KwIn
            | BaseTokenKind::KwIs
            | BaseTokenKind::KwAsync
            | BaseTokenKind::KwAwait
            | BaseTokenKind::KwYield
            | BaseTokenKind::KwSelf
            | BaseTokenKind::KwSuper
            | BaseTokenKind::KwNew => TokenCategory::Keyword,

            // Operators
            BaseTokenKind::Plus
            | BaseTokenKind::Minus
            | BaseTokenKind::Star
            | BaseTokenKind::Slash
            | BaseTokenKind::Percent
            | BaseTokenKind::DoubleStar
            | BaseTokenKind::Eq
            | BaseTokenKind::NotEq
            | BaseTokenKind::Lt
            | BaseTokenKind::Gt
            | BaseTokenKind::LtEq
            | BaseTokenKind::GtEq
            | BaseTokenKind::Assign
            | BaseTokenKind::PlusAssign
            | BaseTokenKind::MinusAssign
            | BaseTokenKind::StarAssign
            | BaseTokenKind::SlashAssign
            | BaseTokenKind::Ampersand
            | BaseTokenKind::Pipe
            | BaseTokenKind::DoubleAmp
            | BaseTokenKind::DoublePipe
            | BaseTokenKind::Caret
            | BaseTokenKind::Tilde
            | BaseTokenKind::Arrow
            | BaseTokenKind::FatArrow => TokenCategory::Operator,

            // Delimiters
            BaseTokenKind::LParen
            | BaseTokenKind::RParen
            | BaseTokenKind::LBracket
            | BaseTokenKind::RBracket
            | BaseTokenKind::LBrace
            | BaseTokenKind::RBrace => TokenCategory::Delimiter,

            // Punctuation
            BaseTokenKind::Comma
            | BaseTokenKind::Colon
            | BaseTokenKind::DoubleColon
            | BaseTokenKind::Semicolon
            | BaseTokenKind::Dot
            | BaseTokenKind::DoubleDot
            | BaseTokenKind::DoubleDotEq
            | BaseTokenKind::Ellipsis
            | BaseTokenKind::Question
            | BaseTokenKind::DoubleQuestion
            | BaseTokenKind::QuestionDot
            | BaseTokenKind::At
            | BaseTokenKind::Hash
            | BaseTokenKind::Dollar
            | BaseTokenKind::Backslash
            | BaseTokenKind::Underscore => TokenCategory::Punctuation,

            // Whitespace
            BaseTokenKind::Newline | BaseTokenKind::Indent | BaseTokenKind::Dedent => {
                TokenCategory::Whitespace
            }

            // Comments
            BaseTokenKind::Comment => TokenCategory::Comment,
            BaseTokenKind::DocComment => TokenCategory::DocComment,

            // Special
            BaseTokenKind::Eof => TokenCategory::Eof,
            BaseTokenKind::Error => TokenCategory::Error,
        }
    }

    /// Get the display name for this token kind
    pub fn name(&self) -> &'static str {
        match self {
            BaseTokenKind::Integer => "integer",
            BaseTokenKind::Float => "float",
            BaseTokenKind::String => "string",
            BaseTokenKind::Bool => "bool",
            BaseTokenKind::Null => "null",
            BaseTokenKind::Identifier => "identifier",
            BaseTokenKind::KwTrue => "true",
            BaseTokenKind::KwFalse => "false",
            BaseTokenKind::KwNull => "null",
            BaseTokenKind::KwVal => "val",
            BaseTokenKind::KwVar => "var",
            BaseTokenKind::KwLet => "let",
            BaseTokenKind::KwMut => "mut",
            BaseTokenKind::KwConst => "const",
            BaseTokenKind::KwFn => "fn",
            BaseTokenKind::KwReturn => "return",
            BaseTokenKind::KwIf => "if",
            BaseTokenKind::KwElse => "else",
            BaseTokenKind::KwElif => "elif",
            BaseTokenKind::KwFor => "for",
            BaseTokenKind::KwWhile => "while",
            BaseTokenKind::KwLoop => "loop",
            BaseTokenKind::KwBreak => "break",
            BaseTokenKind::KwContinue => "continue",
            BaseTokenKind::KwMatch => "match",
            BaseTokenKind::KwCase => "case",
            BaseTokenKind::KwStruct => "struct",
            BaseTokenKind::KwClass => "class",
            BaseTokenKind::KwEnum => "enum",
            BaseTokenKind::KwTrait => "trait",
            BaseTokenKind::KwImpl => "impl",
            BaseTokenKind::KwType => "type",
            BaseTokenKind::KwPub => "pub",
            BaseTokenKind::KwPriv => "priv",
            BaseTokenKind::KwImport => "import",
            BaseTokenKind::KwExport => "export",
            BaseTokenKind::KwFrom => "from",
            BaseTokenKind::KwAs => "as",
            BaseTokenKind::KwMod => "mod",
            BaseTokenKind::KwUse => "use",
            BaseTokenKind::KwAnd => "and",
            BaseTokenKind::KwOr => "or",
            BaseTokenKind::KwNot => "not",
            BaseTokenKind::KwIn => "in",
            BaseTokenKind::KwIs => "is",
            BaseTokenKind::KwAsync => "async",
            BaseTokenKind::KwAwait => "await",
            BaseTokenKind::KwYield => "yield",
            BaseTokenKind::KwSelf => "self",
            BaseTokenKind::KwSuper => "super",
            BaseTokenKind::KwNew => "new",
            BaseTokenKind::Plus => "+",
            BaseTokenKind::Minus => "-",
            BaseTokenKind::Star => "*",
            BaseTokenKind::Slash => "/",
            BaseTokenKind::Percent => "%",
            BaseTokenKind::DoubleStar => "**",
            BaseTokenKind::Eq => "==",
            BaseTokenKind::NotEq => "!=",
            BaseTokenKind::Lt => "<",
            BaseTokenKind::Gt => ">",
            BaseTokenKind::LtEq => "<=",
            BaseTokenKind::GtEq => ">=",
            BaseTokenKind::Assign => "=",
            BaseTokenKind::PlusAssign => "+=",
            BaseTokenKind::MinusAssign => "-=",
            BaseTokenKind::StarAssign => "*=",
            BaseTokenKind::SlashAssign => "/=",
            BaseTokenKind::Ampersand => "&",
            BaseTokenKind::Pipe => "|",
            BaseTokenKind::DoubleAmp => "&&",
            BaseTokenKind::DoublePipe => "||",
            BaseTokenKind::Caret => "^",
            BaseTokenKind::Tilde => "~",
            BaseTokenKind::Arrow => "->",
            BaseTokenKind::FatArrow => "=>",
            BaseTokenKind::LParen => "(",
            BaseTokenKind::RParen => ")",
            BaseTokenKind::LBracket => "[",
            BaseTokenKind::RBracket => "]",
            BaseTokenKind::LBrace => "{",
            BaseTokenKind::RBrace => "}",
            BaseTokenKind::Comma => ",",
            BaseTokenKind::Colon => ":",
            BaseTokenKind::DoubleColon => "::",
            BaseTokenKind::Semicolon => ";",
            BaseTokenKind::Dot => ".",
            BaseTokenKind::DoubleDot => "..",
            BaseTokenKind::DoubleDotEq => "..=",
            BaseTokenKind::Ellipsis => "...",
            BaseTokenKind::Question => "?",
            BaseTokenKind::DoubleQuestion => "??",
            BaseTokenKind::QuestionDot => "?.",
            BaseTokenKind::At => "@",
            BaseTokenKind::Hash => "#",
            BaseTokenKind::Dollar => "$",
            BaseTokenKind::Backslash => "\\",
            BaseTokenKind::Underscore => "_",
            BaseTokenKind::Newline => "newline",
            BaseTokenKind::Indent => "INDENT",
            BaseTokenKind::Dedent => "DEDENT",
            BaseTokenKind::Comment => "comment",
            BaseTokenKind::DocComment => "doc_comment",
            BaseTokenKind::Eof => "EOF",
            BaseTokenKind::Error => "error",
        }
    }

    /// Check if this is a keyword token
    pub fn is_keyword(&self) -> bool {
        matches!(
            self.category(),
            TokenCategory::Keyword | TokenCategory::ControlFlow | TokenCategory::TypeKeyword
        )
    }

    /// Check if this is an operator token
    pub fn is_operator(&self) -> bool {
        self.category() == TokenCategory::Operator
    }

    /// Check if this is a literal token
    pub fn is_literal(&self) -> bool {
        matches!(
            self.category(),
            TokenCategory::IntegerLiteral
                | TokenCategory::FloatLiteral
                | TokenCategory::StringLiteral
                | TokenCategory::BoolLiteral
                | TokenCategory::NullLiteral
        )
    }
}

//==============================================================================
// High-Level Constraint Operations
//==============================================================================

/// High-level operations that both interpreter and compiler understand
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum HighLevelOp {
    /// Type assertion at runtime
    TypeAssert {
        expected: String,
    },
    /// Capability check (mut, iso, etc.)
    CapabilityCheck {
        capability: String,
    },
    /// Effect boundary (IO, Async, etc.)
    EffectBoundary {
        effect: String,
    },
    /// Contract precondition
    Precondition {
        condition: String,
    },
    /// Contract postcondition
    Postcondition {
        condition: String,
    },
    /// Class invariant check
    Invariant {
        condition: String,
    },
}

//==============================================================================
// Tests
//==============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_log_level() {
        assert_eq!(LogLevel::from_u8(0), LogLevel::Off);
        assert_eq!(LogLevel::from_u8(4), LogLevel::Info);
        assert_eq!(LogLevel::from_u8(10), LogLevel::All);
        assert_eq!(LogLevel::Info.name(), "info");
    }

    #[test]
    fn test_primitive_size() {
        assert_eq!(PrimitiveKind::Bool.size(), 1);
        assert_eq!(PrimitiveKind::I64.size(), 8);
        assert_eq!(PrimitiveKind::F64.size(), 8);
    }

    #[test]
    fn test_struct_layout() {
        let mut layout = StructLayout::new("Point");
        layout.add_field("x", 8, 8); // i64
        layout.add_field("y", 8, 8); // i64
        layout.finalize();

        assert_eq!(layout.size, 16);
        assert_eq!(layout.align, 8);
        assert_eq!(layout.field_index("x"), Some(0));
        assert_eq!(layout.field_index("y"), Some(1));
        assert_eq!(layout.field("x").unwrap().offset, 0);
        assert_eq!(layout.field("y").unwrap().offset, 8);
    }

    #[test]
    fn test_struct_layout_with_padding() {
        let mut layout = StructLayout::new("Mixed");
        layout.add_field("a", 1, 1); // bool
        layout.add_field("b", 8, 8); // i64 (needs padding)
        layout.add_field("c", 1, 1); // bool
        layout.finalize();

        assert_eq!(layout.field("a").unwrap().offset, 0);
        assert_eq!(layout.field("b").unwrap().offset, 8); // Aligned to 8
        assert_eq!(layout.field("c").unwrap().offset, 16);
        assert_eq!(layout.size, 24); // Aligned to 8
    }

    #[test]
    fn test_enum_layout() {
        let mut layout = EnumLayout::new("Option");
        layout.add_variant(VariantLayout::unit("None", 0));
        layout.add_variant(VariantLayout::with_payload(
            "Some",
            1,
            vec![FieldLayout::new("value", 0, 8, 8)],
        ));
        layout.finalize();

        assert_eq!(layout.variants.len(), 2);
        assert_eq!(layout.discriminant("None"), Some(0));
        assert_eq!(layout.discriminant("Some"), Some(1));
        assert!(layout.size >= 9); // 1 byte tag + 8 byte payload
    }

    #[test]
    fn test_token_category() {
        assert_eq!(TokenCategory::Keyword.css_class(), "keyword");
        assert_eq!(TokenCategory::StringLiteral.css_class(), "string");
        assert_eq!(TokenCategory::Operator.treesitter_scope(), "operator");
        assert_eq!(
            TokenCategory::IntegerLiteral.treesitter_scope(),
            "constant.numeric.integer"
        );
    }

    #[test]
    fn test_base_token_kind_category() {
        assert_eq!(BaseTokenKind::Integer.category(), TokenCategory::IntegerLiteral);
        assert_eq!(BaseTokenKind::KwFn.category(), TokenCategory::Keyword);
        assert_eq!(BaseTokenKind::KwIf.category(), TokenCategory::ControlFlow);
        assert_eq!(BaseTokenKind::KwStruct.category(), TokenCategory::TypeKeyword);
        assert_eq!(BaseTokenKind::Plus.category(), TokenCategory::Operator);
        assert_eq!(BaseTokenKind::LParen.category(), TokenCategory::Delimiter);
        assert_eq!(BaseTokenKind::Comma.category(), TokenCategory::Punctuation);
    }

    #[test]
    fn test_base_token_kind_name() {
        assert_eq!(BaseTokenKind::KwFn.name(), "fn");
        assert_eq!(BaseTokenKind::Plus.name(), "+");
        assert_eq!(BaseTokenKind::LParen.name(), "(");
        assert_eq!(BaseTokenKind::Arrow.name(), "->");
        assert_eq!(BaseTokenKind::DoubleQuestion.name(), "??");
    }

    #[test]
    fn test_base_token_kind_predicates() {
        assert!(BaseTokenKind::KwFn.is_keyword());
        assert!(BaseTokenKind::KwIf.is_keyword());
        assert!(BaseTokenKind::KwStruct.is_keyword());
        assert!(!BaseTokenKind::Plus.is_keyword());

        assert!(BaseTokenKind::Plus.is_operator());
        assert!(BaseTokenKind::Eq.is_operator());
        assert!(!BaseTokenKind::KwFn.is_operator());

        assert!(BaseTokenKind::Integer.is_literal());
        assert!(BaseTokenKind::String.is_literal());
        assert!(BaseTokenKind::Bool.is_literal());
        assert!(!BaseTokenKind::KwFn.is_literal());
    }
}
