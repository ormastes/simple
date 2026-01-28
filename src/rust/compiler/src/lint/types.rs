//! Lint type definitions and enumerations.
//!
//! #![skip_todo]

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
    /// Print calls in test spec files
    PrintInTestSpec,
    /// Improperly formatted TODO/FIXME comments
    TodoFormat,
    /// Print-based BDD tests (use proper SSpec syntax)
    SSpecNoPrintBasedTests,
    /// Missing docstrings in describe/context/it blocks
    SSpecMissingDocstrings,
    /// Files with minimal docstring usage
    SSpecMinimalDocstrings,
    /// Manual pass/fail tracking instead of expect()
    SSpecManualAssertions,
    /// Positional arguments for parameters that share a type with other parameters
    UnnamedDuplicateTypedArgs,
    /// Resource types not properly closed within scope
    ResourceLeak,
    /// Wildcard `_` pattern used in match arms
    WildcardMatch,
    /// Not all enum/option variants explicitly listed in match
    NonExhaustiveMatch,
}

impl LintName {
    /// Get the string name of the lint
    pub fn as_str(&self) -> &'static str {
        match self {
            LintName::PrimitiveApi => "primitive_api",
            LintName::BareBool => "bare_bool",
            LintName::PrintInTestSpec => "print_in_test_spec",
            LintName::TodoFormat => "todo_format",
            LintName::SSpecNoPrintBasedTests => "sspec_no_print_based_tests",
            LintName::SSpecMissingDocstrings => "sspec_missing_docstrings",
            LintName::SSpecMinimalDocstrings => "sspec_minimal_docstrings",
            LintName::SSpecManualAssertions => "sspec_manual_assertions",
            LintName::UnnamedDuplicateTypedArgs => "unnamed_duplicate_typed_args",
            LintName::ResourceLeak => "resource_leak",
            LintName::WildcardMatch => "wildcard_match",
            LintName::NonExhaustiveMatch => "non_exhaustive_match",
        }
    }

    /// Parse lint name from string
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "primitive_api" => Some(LintName::PrimitiveApi),
            "bare_bool" => Some(LintName::BareBool),
            "print_in_test_spec" => Some(LintName::PrintInTestSpec),
            "todo_format" => Some(LintName::TodoFormat),
            "sspec_no_print_based_tests" => Some(LintName::SSpecNoPrintBasedTests),
            "sspec_missing_docstrings" => Some(LintName::SSpecMissingDocstrings),
            "sspec_minimal_docstrings" => Some(LintName::SSpecMinimalDocstrings),
            "sspec_manual_assertions" => Some(LintName::SSpecManualAssertions),
            "unnamed_duplicate_typed_args" => Some(LintName::UnnamedDuplicateTypedArgs),
            "resource_leak" => Some(LintName::ResourceLeak),
            "wildcard_match" => Some(LintName::WildcardMatch),
            "non_exhaustive_match" => Some(LintName::NonExhaustiveMatch),
            _ => None,
        }
    }

    /// Get the default level for this lint
    pub fn default_level(&self) -> LintLevel {
        match self {
            LintName::PrimitiveApi => LintLevel::Warn,
            LintName::BareBool => LintLevel::Warn,
            LintName::PrintInTestSpec => LintLevel::Warn,
            LintName::TodoFormat => LintLevel::Warn,
            // SSpec lints: no_print_based_tests is Deny (error), others are Warn
            LintName::SSpecNoPrintBasedTests => LintLevel::Deny,
            LintName::SSpecMissingDocstrings => LintLevel::Warn,
            LintName::SSpecMinimalDocstrings => LintLevel::Warn, // Info level not supported, use Warn
            LintName::SSpecManualAssertions => LintLevel::Warn,
            LintName::UnnamedDuplicateTypedArgs => LintLevel::Warn,
            LintName::ResourceLeak => LintLevel::Warn,
            LintName::WildcardMatch => LintLevel::Allow,
            LintName::NonExhaustiveMatch => LintLevel::Warn,
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
            LintName::PrimitiveApi => r#"Lint: primitive_api
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
"#
            .to_string(),
            LintName::BareBool => r#"Lint: bare_bool
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
"#
            .to_string(),
            LintName::PrintInTestSpec => r#"Lint: print_in_test_spec
Level: warn (default)

=== What it checks ===

This lint warns when `print()` function calls are used in test specification
files (files ending with `_spec.spl`).

=== Why it matters ===

Test specs should use triple-quoted strings for documentation output rather
than print statements. This makes test output clearer and more maintainable.

Print statements in test specs create noise and make it harder to distinguish
between test documentation and actual test results.

=== Examples ===

Triggers the lint:
    # In some_feature_spec.spl
    print("Testing feature X")
    print("  should work correctly")

Does not trigger:
    # In regular code (not _spec.spl)
    print("Debug output")

    # In _spec.spl with explicit allow
    #[allow(print_in_test_spec)]
    fn debug_helper():
        print("Debug info")

=== How to fix ===

1. Use triple-quoted strings for test documentation:
    """
    Testing feature X
      should work correctly
    """

2. If print is genuinely needed (e.g., debugging), add an attribute:
    #[allow(print_in_test_spec)]
    fn debug_test():
        print("Debug output")

=== How to suppress ===

    #[allow(print_in_test_spec)]
    fn test_with_print():
        print("Needed for this test")

Or in simple.sdn:
    [lints]
    print_in_test_spec = "allow"
"#
            .to_string(),
            LintName::TodoFormat => r#"Lint: todo_format
Level: warn (default)

=== What it checks ===

This lint warns when TODO or FIXME comments don't follow the required format:
    TODO: [area][priority] description [#issue] [blocked:#issue,#issue]

=== Why it matters ===

Consistent TODO formatting enables:
- Automated tracking and reporting
- Priority-based categorization
- Area-based filtering
- Dependency management via blocked tags
- Integration with issue trackers

Unformatted TODOs are hard to track and often forgotten.

=== Examples ===

Triggers the lint:
    # TODO: implement this feature
    # TODO implement socket write
    # FIXME: broken

Does not trigger:
    # TODO: [runtime][P1] Implement monoio TCP write [#234]
    # TODO: [stdlib][P0] Fix memory leak [#567] [blocked:#123]
    # TODO: [codegen][P2] Add SPIR-V validation
    # FIXME: [parser][critical] Incorrect parsing [#890]

=== How to fix ===

Use the required format with:
- Keyword: TODO: or FIXME:
- Area: [runtime, codegen, compiler, parser, type, stdlib, gpu, ui, test, driver, loader, pkg, doc]
- Priority: [P0/critical, P1/high, P2/medium, P3/low]
- Description: Clear explanation
- Optional: [#issue] for issue tracking
- Optional: [blocked:#123,#456] for dependencies

Examples:
    # TODO: [runtime][P0] Implement monoio TCP write [#234]
    # TODO: [stdlib][critical] Fix memory corruption [#567]
    # TODO: [gpu][P1] Create Vector3 variant [#789] [blocked:#100]
    # FIXME: [parser][P2] Handle edge case in expression parsing

=== How to suppress ===

If you have a TODO that doesn't fit the format (rare):
    #[allow(todo_format)]

Or in simple.sdn:
    [lints]
    todo_format = "allow"

See also: .claude/skills/todo.md for full format specification
"#
            .to_string(),
            LintName::SSpecNoPrintBasedTests => "Lint: sspec_no_print_based_tests\nLevel: deny\n\nDetects print-based assertions in SSpec tests. Use expect() matchers instead.".to_string(),
            LintName::SSpecMissingDocstrings => "Lint: sspec_missing_docstrings\nLevel: warn\n\nWarns when describe/context/it blocks lack docstrings.".to_string(),
            LintName::SSpecMinimalDocstrings => "Lint: sspec_minimal_docstrings\nLevel: warn\n\nWarns when test files have minimal documentation.".to_string(),
            LintName::SSpecManualAssertions => "Lint: sspec_manual_assertions\nLevel: warn\n\nDetects manual pass/fail tracking instead of expect() assertions.".to_string(),
            LintName::UnnamedDuplicateTypedArgs => r#"Lint: unnamed_duplicate_typed_args
Level: warn (default)

=== What it checks ===

This lint warns when a function has multiple parameters with the same type
and any of those parameters are passed positionally (not named) at the call site.

=== Why it matters ===

When multiple parameters share the same type, it's easy to accidentally swap
arguments without the compiler catching it:

    fn create_user(name: text, email: text, phone: text):
        ...

    # Bug: arguments in wrong order, but compiles fine!
    create_user("john@example.com", "John", "555-1234")

Named arguments make intent explicit and prevent such bugs:

    create_user(name: "John", email: "john@example.com", phone: "555-1234")

=== Examples ===

Triggers the lint:
    fn point(x: i64, y: i64):
        ...
    point(3, 4)              # x, y share type i64
    point(x: 3, 4)           # y is positional

Does not trigger:
    point(x: 3, y: 4)        # All same-typed params are named
    point(y: 4, x: 3)        # Order doesn't matter with names

    fn describe(name: text, age: i64):
        ...
    describe("Alice", 30)    # Types are different, no confusion

=== How to fix ===

Use named arguments for parameters that share a type:

    # Instead of:
    point(3, 4)

    # Use:
    point(x: 3, y: 4)

=== How to suppress ===

If positional arguments are intentional:

    #[allow(unnamed_duplicate_typed_args)]
    fn swap(a: i64, b: i64):
        ...

Or in simple.sdn:
    [lints]
    unnamed_duplicate_typed_args = "allow"
"#.to_string(),
            LintName::ResourceLeak => r#"Lint: resource_leak
Level: warn (default)

=== What it checks ===

This lint warns when a Resource-typed variable is created but not properly
closed within its scope. Resources include File, TcpStream, TcpListener,
UdpSocket, and other types implementing the Resource trait.

=== Why it matters ===

Unclosed resources can lead to:
- File handle exhaustion
- Socket/port leaks
- Memory leaks
- System resource exhaustion
- Test failures due to lingering resources

Proper resource cleanup is essential for reliable software.

=== Examples ===

Triggers the lint:
    fn process_file():
        val file = File.open("data.txt")  # Warning: file not closed
        val content = file.read()
        # Missing: file.close()

    fn connect():
        val conn = TcpStream.connect("localhost:8080")  # Warning
        conn.write("hello")
        # Missing: conn.close()

Does not trigger:
    fn process_file():
        val file = File.open("data.txt")
        val content = file.read()
        file.close()  # Properly closed

    fn connect():
        with TcpStream.connect("localhost:8080") as conn:
            conn.write("hello")
        # Automatically closed by with statement

    fn with_defer():
        val file = File.open("data.txt")
        defer file.close()  # Will be closed at scope exit
        val content = file.read()

=== How to fix ===

1. Explicitly close resources:
    val file = File.open("path")
    defer file.close()  # Best practice
    # ... use file ...

2. Use with/using statement for automatic cleanup:
    with File.open("path") as file:
        val content = file.read()
    # file.close() called automatically

3. Use the resource BDD fixture in tests:
    resource :db, \: Database.connect("test.db")
    it "queries data":
        db.execute("SELECT 1")
    # db.close() called automatically after each test

=== How to suppress ===

If the resource is intentionally left open (e.g., returned to caller):

    #[allow(resource_leak)]
    fn create_connection() -> TcpStream:
        TcpStream.connect("localhost:8080")  # Caller is responsible

Or in simple.sdn:
    [lints]
    resource_leak = "allow"
"#.to_string(),
        }
    }

    /// Get all available lint names
    pub fn all_lints() -> Vec<Self> {
        vec![
            LintName::PrimitiveApi,
            LintName::BareBool,
            LintName::PrintInTestSpec,
            LintName::TodoFormat,
            LintName::SSpecNoPrintBasedTests,
            LintName::SSpecMissingDocstrings,
            LintName::SSpecMinimalDocstrings,
            LintName::SSpecManualAssertions,
            LintName::UnnamedDuplicateTypedArgs,
            LintName::ResourceLeak,
        ]
    }
}
