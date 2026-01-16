/// Naming pattern for variables and identifiers
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NamePattern {
    /// ALL_CAPS - compile-time constant, non-rebindable
    Constant,
    /// PascalCase - type name (class, struct, enum, trait)
    TypeName,
    /// lowercase - immutable variable, supports functional update (->)
    Immutable,
    /// ends with _ - mutable variable, supports reassignment
    Mutable,
    /// starts with _ - private member (visibility, not mutability)
    Private,
}

impl NamePattern {
    /// Detect the naming pattern from an identifier string
    pub fn detect(name: &str) -> Self {
        if name.is_empty() {
            return NamePattern::Immutable;
        }

        // Private: starts with underscore
        if name.starts_with('_') {
            return NamePattern::Private;
        }

        // Mutable: ends with underscore
        if name.ends_with('_') {
            return NamePattern::Mutable;
        }

        // Check if ALL_CAPS (all uppercase letters, numbers, and underscores)
        let is_all_caps = name.chars().all(|c| c.is_uppercase() || c.is_numeric() || c == '_');

        if is_all_caps && name.chars().any(|c| c.is_alphabetic()) {
            return NamePattern::Constant;
        }

        // TypeName: starts with uppercase
        if name.chars().next().map_or(false, |c| c.is_uppercase()) {
            return NamePattern::TypeName;
        }

        // Default: lowercase immutable variable
        NamePattern::Immutable
    }
}

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
        Self {
            start,
            end,
            line,
            column,
        }
    }
}

/// Part of an f-string token (for interpolated strings)
#[derive(Debug, Clone, PartialEq)]
pub enum FStringToken {
    Literal(String),
    Expr(String), // The expression text to be parsed later
}

/// Numeric type suffix for typed literals
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NumericSuffix {
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
    Unit(String), // User-defined unit suffix like _km, _hr
}

/// Token types for the Simple language
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    Integer(i64),
    Float(f64),
    TypedInteger(i64, NumericSuffix),
    TypedFloat(f64, NumericSuffix),
    String(String),                 // Legacy: plain string (for backward compat)
    FString(Vec<FStringToken>),     // "hello {expr}" interpolated strings (now default for double quotes)
    RawString(String),              // 'raw string' - no escapes, no interpolation
    TypedString(String, String),    // "value"_suffix - string with unit suffix (e.g., "127.0.0.1"_ip)
    TypedRawString(String, String), // 'value'_suffix - raw string with unit suffix
    Bool(bool),
    Nil,
    Symbol(String), // :symbol

    /// i18n named string: Name_"text"
    I18nString {
        name: String,
        default_text: String,
    },
    /// i18n string with template interpolations: Name_"text with {var}"
    I18nFString {
        name: String,
        parts: Vec<FStringToken>,
    },

    // Identifiers and Keywords
    Identifier {
        name: String,
        pattern: NamePattern,
    },

    // Keywords
    Fn,
    Me,  // Mutable method (modifies self)
    Let, // Legacy: use Val instead
    Mut, // Legacy: will be removed
    Val, // Immutable variable (Scala-style)
    Var, // Mutable variable (Scala-style)
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
    Case,

    // Suspension control flow (async-by-default #45)
    IfSuspend,    // if~ (suspension if statement)
    WhileSuspend, // while~ (suspension while loop)
    ForSuspend,   // for~ (suspension for loop)
    Struct,
    Class,
    Enum,
    Union, // union (tagged union, alias for enum with data)
    Trait,
    Impl,
    Mixin, // mixin (for mixin declarations, Feature #2200)
    Actor,
    Extends, // extends (class inheritance)
    Pub,
    Priv,
    Import,
    From,
    As,
    Mod,    // mod (module declaration)
    Use,    // use (import)
    Export, // export (re-export)
    Common, // common (directory prelude)
    Auto,   // auto (auto import)
    Crate,  // crate (module root)
    In,
    Is,
    Not,
    And,
    Or,
    True,
    False,
    Spawn,
    Go, // go (Go-style thread spawn syntax)
    New,
    Self_,
    Super,
    Async,
    Await,
    Sync,
    Yield,
    Move,
    Const,
    Static,
    Type,
    Unit, // unit (for unit type definitions)
    Extern,
    Context,
    With,  // with (for context managers)
    Ghost, // ghost (verification-only code, erased at runtime)
    Macro,
    Bang,   // ! (for macro invocations)
    Vec,    // vec (for SIMD vector types)
    Shared, // shared (for GPU shared memory)
    Gpu,    // gpu (for GPU intrinsics namespace)
    Bounds, // bounds (for @simd kernel bounds: clause)
    Dyn,    // dyn (for dynamic trait objects)
    Repr,   // repr (for unit representation constraints)
    // Note: 'allow' is parsed as identifier (not a keyword) to avoid conflict with #[allow(...)]
    // Note: 'checked', 'saturate', 'wrap', 'range' are parsed as identifiers in where clauses

    // AOP & Unified Predicates (#1000-1050)
    Pointcut(String), // pc{...} predicate expression (stores the inner content)
    On,               // on (for AOP advice: `on pc{...} use Interceptor`)
    Bind,             // bind (for DI: `bind on pc{...} -> Impl`)
    Forbid,           // forbid (for architecture rules: `forbid pc{...}`)
    Allow,            // allow (keyword for architecture rules: `allow pc{...}`)
    Mock,             // mock (for mock declarations: `mock Name implements Trait:`)

    // Custom Blocks (#1090-1098)
    // DSL embedding blocks: kind{payload} where payload is captured raw
    CustomBlock {
        kind: String,    // Block kind: "m", "sh", "sql", "re", "md", "html", "graph", "img"
        payload: String, // Raw payload content (not parsed by outer lexer)
    },

    // Contract keywords (LLM-friendly features)
    // New spec syntax (doc/spec/invariant.md)
    Out,    // out (postcondition block)
    OutErr, // out_err (error postcondition block)
    Where,  // where (refinement type predicate)
    // Legacy syntax (still supported)
    Requires, // requires: (precondition) - legacy, use in:
    Ensures,  // ensures: (postcondition) - legacy, use out(ret):
    // Shared
    Invariant, // invariant: (routine/class invariant)
    Old,       // old() (previous value in postconditions)
    Result,    // result (return value in ensures) - legacy
    Decreases, // decreases: (termination measure for Lean verification)

    // Infix keywords (for BDD spec framework)
    // These parse as infix method calls: `A to B` → `A.to(B)`
    To,    // to (positive assertion: expect x to eq 5)
    NotTo, // not_to (negative assertion: expect x not_to eq 5)

    // Gherkin-style system test DSL keywords (doc/spec/gherkin_dsl.md)
    Feature,  // feature Name: (test grouping)
    Scenario, // scenario Name: or scenario outline Name:
    Outline,  // outline (modifier for scenario)
    Examples, // examples name: (data table with two-space delimiter)
    Given,    // given step_pattern: (setup step)
    When,     // when step_pattern: (action step)
    Then,     // then step_pattern: (assertion step)
    AndThen,  // and_then step_pattern: (chained assertion)

    // Memory management keywords
    HandlePool, // handle_pool (declare a handle pool for a type)

    // Simple Math keywords (#1910-#1969)
    Grid,    // grid (2D matrix literal)
    Tensor,  // tensor (N-D tensor literal)
    Slice,   // slice (tensor slice block)
    Flat,    // flat (sparse tensor mode)
    Default, // default (default value for sparse tensors)

    // Operators
    Plus,        // +
    Minus,       // -
    Star,        // *
    Slash,       // /
    Percent,     // %
    DoubleStar,  // **
    DoubleSlash, // //

    Eq,    // ==
    NotEq, // !=
    Lt,    // <
    Gt,    // >
    LtEq,  // <=
    GtEq,  // >=

    Assign,      // =
    PlusAssign,  // +=
    MinusAssign, // -=
    StarAssign,  // *=
    SlashAssign, // /=
    TildeAssign, // ~= (suspension assignment for async-by-default)

    Ampersand,  // &
    Pipe,       // |
    DoublePipe, // ||
    DoubleAmp,  // &&
    Caret,      // ^
    Tilde,      // ~
    ShiftLeft,  // <<
    ShiftRight, // >>

    Arrow,        // ->
    FatArrow,     // =>
    ChannelArrow, // <-

    // Delimiters
    LParen,   // (
    RParen,   // )
    LBracket, // [
    RBracket, // ]
    LBrace,   // {
    RBrace,   // }

    Comma,       // ,
    Colon,       // :
    DoubleColon, // ::
    Semicolon,   // ;
    Dot,         // .
    DoubleDot,   // ..
    DoubleDotEq, // ..=
    Ellipsis,    // ...
    Question,    // ?
    At,          // @
    Hash,        // #
    Dollar,      // $
    Backslash,   // \
    Underscore,  // _ (as pattern)

    // Indentation tokens
    Newline,
    Indent,
    Dedent,

    // Documentation
    DocComment(String), // /** ... */ or ## line comment

    // Special
    Eof,
    Error(String),
}

impl TokenKind {
    /// Returns true if this is an identifier token
    pub fn is_identifier(&self) -> bool {
        matches!(self, TokenKind::Identifier { .. })
    }

    /// Get the identifier name if this is an Identifier token
    pub fn as_identifier(&self) -> Option<&str> {
        match self {
            TokenKind::Identifier { name, .. } => Some(name),
            _ => None,
        }
    }

    /// Get the identifier name and pattern if this is an Identifier token
    pub fn as_identifier_with_pattern(&self) -> Option<(&str, NamePattern)> {
        match self {
            TokenKind::Identifier { name, pattern } => Some((name, *pattern)),
            _ => None,
        }
    }

    /// Check if this is an identifier with a specific name
    pub fn is_identifier_named(&self, expected: &str) -> bool {
        matches!(self, TokenKind::Identifier { name, .. } if name == expected)
    }
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
        let token = Token::new(TokenKind::Integer(42), Span::new(0, 2, 1, 1), "42".to_string());
        assert_eq!(token.kind, TokenKind::Integer(42));
        assert_eq!(token.lexeme, "42");
    }
}
