# I18n CLI Integration Guide

This guide explains how to integrate the i18n diagnostics system into Simple's CLI commands.

## Current Status

✅ **Infrastructure Complete:**
- `simple-diagnostics` crate with i18n support
- `simple_i18n` with message catalogs
- Conversion helpers in `simple-driver`
- CLI `--lang` flag parsing

❌ **Not Yet Integrated:**
- CLI commands still use old error display
- Need to wire up conversion helpers

## Integration Steps

### Step 1: Update `src/driver/src/cli/check.rs`

#### Current Code (Lines 172-174)
```rust
Err(e) => {
    // Convert ParseError to CheckError
    errors.push(parse_error_to_check_error(&e, path));
}
```

#### New Code (with i18n)
```rust
Err(e) => {
    // Convert ParseError to i18n diagnostic
    use simple_driver::convert_parser_diagnostic;
    let i18n_diag = convert_parser_diagnostic(&e);

    // Convert to CheckError for now (temporary bridge)
    errors.push(CheckError {
        file: path.display().to_string(),
        line: i18n_diag.span.map(|s| s.line).unwrap_or(0),
        column: i18n_diag.span.map(|s| s.column).unwrap_or(0),
        severity: match i18n_diag.severity {
            simple_diagnostics::Severity::Error => ErrorSeverity::Error,
            _ => ErrorSeverity::Warning,
        },
        message: i18n_diag.message.clone(),
        expected: None,
        found: None,
    });
}
```

### Step 2: Update Error Display (Lines 342-367)

#### Current Code
```rust
fn print_error(error: &CheckError) {
    let color = match error.severity {
        ErrorSeverity::Error => "\x1b[31m",
        ErrorSeverity::Warning => "\x1b[33m",
    };
    // ... manual formatting
}
```

#### New Code (with i18n)
```rust
fn print_error_i18n(diag: &simple_diagnostics::Diagnostic, source: &str) {
    use simple_diagnostics::formatters::TextFormatter;

    let formatter = TextFormatter::new();
    let output = formatter.format(diag, source);
    println!("{}", output);
}
```

### Step 3: Full Refactor (Recommended Long-term)

Replace `CheckError` entirely with `simple_diagnostics::Diagnostic`:

```rust
// OLD
pub struct CheckResult {
    pub file: String,
    pub status: CheckStatus,
    pub errors: Vec<CheckError>,  // OLD
}

// NEW
pub struct CheckResult {
    pub file: String,
    pub status: CheckStatus,
    pub diagnostics: Vec<simple_diagnostics::Diagnostic>,  // NEW
}
```

## Integration Example

See `src/driver/examples/i18n_error_example.rs` for a complete working example.

### Running the Example

```bash
# English (default)
cargo run --example i18n_error_example

# Korean
cargo run --example i18n_error_example ko

# Output shows:
# - Parser errors in selected language
# - Compiler errors with proper formatting
# - Source code snippets with highlighting
```

## Conversion Helpers Available

### Parser Errors
```rust
use simple_driver::convert_parser_diagnostic;

let parse_error = parser.parse().unwrap_err();
let i18n_diag = convert_parser_diagnostic(&parse_error);
```

### Compiler Errors
```rust
use simple_compiler::convert_compiler_error;
use simple_diagnostics::i18n::ctx2;

// From CompileError
let compile_error = CompileError::semantic_with_context(...);
let i18n_diag = convert_compiler_error(&compile_error);

// Or directly
let ctx = ctx2("name", "foo", "", "");
let diag = Diagnostic::error_i18n("compiler", "E1001", &ctx);
```

## Formatters Available

### Text Formatter (Terminal Output)
```rust
use simple_diagnostics::formatters::TextFormatter;

let formatter = TextFormatter::new();  // with color
let output = formatter.format(&diag, source);
println!("{}", output);

// Without color
let formatter = TextFormatter::without_color();
```

### JSON Formatter (Machine Readable)
```rust
use simple_diagnostics::formatters::JsonFormatter;

let formatter = JsonFormatter::new();  // pretty
let json = formatter.format(&diag);
println!("{}", json);

// Compact
let formatter = JsonFormatter::compact();
```

### Simple Formatter (SSpec Tests)
```rust
use simple_diagnostics::formatters::SimpleFormatter;

let formatter = SimpleFormatter::new();
let output = formatter.format(&diag, source);
```

## Commands That Need Integration

### High Priority
1. **`simple check`** - `src/driver/src/cli/check.rs`
   - Lines 172-174: Parser error conversion
   - Lines 342-367: Error display

2. **`simple build`** - `src/driver/src/cli/basic.rs`
   - Compiler error display

3. **`simple compile`** - `src/driver/src/cli/basic.rs`
   - Compiler error display

### Medium Priority
4. **`simple lint`** - `src/driver/src/cli/code_quality.rs`
   - Lint message display

5. **`simple gen-lean --verify`** - `src/driver/src/cli/gen_lean.rs`
   - Verification error display

### Low Priority
6. REPL error display
7. Test runner error display

## Testing Integration

### Unit Tests
Add tests to verify conversion works:

```rust
#[test]
fn test_parser_error_conversion() {
    env::set_var("SIMPLE_LANG", "ko");

    let source = "fn main():\n    let x =";
    let mut parser = Parser::new(source);
    let err = parser.parse().unwrap_err();

    let diag = convert_parser_diagnostic(&err);
    assert_eq!(diag.code, Some("E0002".to_string()));
    // Message should be in Korean or fallback to English
    assert!(!diag.message.is_empty());
}
```

### Integration Tests
Test full CLI commands:

```bash
# Test Korean errors
SIMPLE_LANG=ko cargo test --package simple-driver test_check_with_errors

# Test English errors
SIMPLE_LANG=en cargo test --package simple-driver test_check_with_errors
```

## Gradual Migration Strategy

### Phase 1: Bridge Pattern (Minimal Changes)
- Keep `CheckError` structure
- Convert i18n diagnostics to `CheckError`
- Update display to use formatted messages
- ✅ No breaking changes
- ✅ I18n works immediately

### Phase 2: Hybrid Approach
- Store both `CheckError` and `Diagnostic`
- Use `Diagnostic` for display
- Keep `CheckError` for compatibility
- ✅ Better formatting
- ⚠️ Some refactoring needed

### Phase 3: Full Migration (Recommended)
- Replace `CheckError` with `Diagnostic` everywhere
- Use formatters exclusively
- Clean up old code
- ✅ Clean architecture
- ✅ Full i18n support
- ⚠️ Significant refactoring

## Estimated Effort

- **Phase 1 (Bridge):** 2-4 hours
- **Phase 2 (Hybrid):** 4-6 hours
- **Phase 3 (Full):** 8-12 hours

## Benefits After Integration

1. **Multilingual Support:** Users see errors in their preferred language
2. **Consistent Formatting:** All errors use same formatter
3. **Better Error Messages:** Rich diagnostics with source snippets
4. **Machine Readable:** JSON output for tools/LLMs
5. **Future Proof:** Easy to add new languages

## References

- **Example Code:** `src/driver/examples/i18n_error_example.rs`
- **Conversion Helpers:** `src/driver/src/diagnostics_conversion.rs`
- **Formatters:** `src/diagnostics/src/formatters/`
- **Catalogs:** `src/i18n/*.spl`
- **Tests:** `src/diagnostics/tests/i18n_integration.rs`

## Getting Help

- **Architecture:** `src/diagnostics/ARCHITECTURE.md`
- **Usage Guide:** `src/diagnostics/USAGE.md`
- **User Guide:** `doc/guide/i18n.md`
- **Contributor Guide:** `doc/contributing/i18n.md`

---

**Status:** Ready for integration
**Last Updated:** 2026-01-19
