//! Lint type definitions and enumerations.

/// Lint severity level
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LintLevel {
    /// Suppress the lint entirely
    Allow,
    /// Emit a warning (default for most lints)
    #[default]
    Warn,
    /// Treat as a compile error
    Deny,
}

impl LintLevel {
    /// Parse lint level from string (attribute value)
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "allow" => Some(LintLevel::Allow),
            "warn" => Some(LintLevel::Warn),
            "deny" => Some(LintLevel::Deny),
            _ => None,
        }
    }
}

/// Known lint names
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LintName {
    /// Bare primitives in public API signatures
    PrimitiveApi,
    /// Bare bool parameters (suggest enum)
    BareBool,
}

impl LintName {
    /// Get the string name of the lint
    pub fn as_str(&self) -> &'static str {
        match self {
            LintName::PrimitiveApi => "primitive_api",
            LintName::BareBool => "bare_bool",
        }
    }

    /// Parse lint name from string
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "primitive_api" => Some(LintName::PrimitiveApi),
            "bare_bool" => Some(LintName::BareBool),
            _ => None,
        }
    }

    /// Get the default level for this lint
    pub fn default_level(&self) -> LintLevel {
        match self {
            LintName::PrimitiveApi => LintLevel::Warn,
            LintName::BareBool => LintLevel::Warn,
        }
    }

    /// Get a detailed explanation of this lint
    ///
    /// Provides:
    /// - What the lint checks for
    /// - Why it matters
    /// - Examples of code that triggers it
    /// - How to fix it
    /// - How to suppress it
    pub fn explain(&self) -> String {
        match self {
            LintName::PrimitiveApi => {
                r#"Lint: primitive_api
Level: warn (default)

=== What it checks ===

This lint warns when bare primitive types (i8, i16, i32, i64, u8, u16, u32, u64,
f32, f64, bool) are used in public API signatures.

=== Why it matters ===

Primitive types lack semantic meaning. For example:

    pub fn set_timeout(value: i64)

What does the i64 represent? Seconds? Milliseconds? A timeout ID?

Using semantic types makes code self-documenting:

    pub fn set_timeout(duration: Duration)

This is immediately clear and prevents errors like passing seconds when
milliseconds are expected.

=== Examples ===

Triggers the lint:
    pub fn calculate(x: i64, y: f64) -> bool
    pub struct Config:
        pub port: i32

Does not trigger:
    fn internal_helper(x: i64) -> bool     # Private function
    pub fn get_name() -> str               # str is allowed
    pub fn find(id: UserId) -> Option[User]  # Semantic types

=== How to fix ===

1. Use semantic unit types:
    unit Duration: i64 as ms
    pub fn set_timeout(duration: Duration)

2. Use newtype wrappers:
    struct UserId(i64)
    pub fn find_user(id: UserId)

3. Use enums for booleans:
    enum CacheMode:
        Enabled
        Disabled
    pub fn configure(cache: CacheMode)

=== How to suppress ===

If you really need primitives in a public API:

    #[allow(primitive_api)]
    pub fn legacy_api(value: i64)

Or in simple.sdn:
    [lints]
    primitive_api = "allow"
"#.to_string()
            }
            LintName::BareBool => {
                r#"Lint: bare_bool
Level: warn (default)

=== What it checks ===

This lint warns when boolean parameters are used in function signatures,
especially public APIs.

=== Why it matters ===

Boolean parameters are unclear at call sites:

    configure(true, false, true)  # What do these mean?

Enums make intent explicit:

    configure(CacheMode::Enabled, LogMode::Disabled, DebugMode::Enabled)

=== Examples ===

Triggers the lint:
    pub fn configure(enable_cache: bool, debug: bool)
    fn process(data: Data, validate: bool)

Does not trigger:
    pub fn configure(mode: CacheMode)
    fn is_valid() -> bool  # Return values are OK

=== How to fix ===

Replace boolean parameters with enums:

    enum CacheMode:
        Enabled
        Disabled

    enum DebugMode:
        Enabled
        Disabled

    pub fn configure(cache: CacheMode, debug: DebugMode)

Call sites become self-documenting:
    configure(CacheMode::Enabled, DebugMode::Disabled)

=== How to suppress ===

If you need boolean parameters:

    #[allow(bare_bool)]
    pub fn set_flag(value: bool)

Or in simple.sdn:
    [lints]
    bare_bool = "allow"
"#.to_string()
            }
        }
    }

    /// Get all available lint names
    pub fn all_lints() -> Vec<Self> {
        vec![LintName::PrimitiveApi, LintName::BareBool]
    }
}
