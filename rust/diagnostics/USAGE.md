# Diagnostics System Usage Guide

## Quick Start

The Simple compiler uses a layered diagnostic architecture:

- **Parser** uses minimal `simple-common::Diagnostic` (no i18n)
- **Driver/Compiler** use `simple-diagnostics::Diagnostic` (full i18n support)
- **Driver** converts parser diagnostics to i18n diagnostics

## Basic Usage in Driver

### 1. Convert Parser Errors

```rust
use simple_driver::convert_parser_diagnostic;
use simple_diagnostics::TextFormatter;

// Get parser error (from simple-common)
let parser_diag = parser.parse_error().to_diagnostic();

// Convert to i18n diagnostic
let i18n_diag = convert_parser_diagnostic(parser_diag);

// Format for terminal output
let source_code = "fn main() { ... }";
let formatter = TextFormatter::new();  // with colors
let output = formatter.format(&i18n_diag, source_code);

eprintln!("{}", output);
```

### 2. Create I18n Diagnostics Directly

```rust
use simple_diagnostics::{Diagnostic, Span, i18n::ctx2};

// Create error with context
let ctx = ctx2("expected", "identifier", "found", "number");
let diag = Diagnostic::error_i18n("parser", "E0002", &ctx)
    .with_span(Span::new(10, 15, 2, 5));

// Format and display
let formatter = TextFormatter::new();
println!("{}", formatter.format(&diag, source_code));
```

### 3. Use Multiple Formatters

```rust
use simple_diagnostics::{Diagnostic, TextFormatter, JsonFormatter, SimpleFormatter};

let diag = /* ... create diagnostic ... */;
let source = "source code here";

// Terminal output (colored)
let text = TextFormatter::new().format(&diag, source);
eprintln!("{}", text);

// JSON output for tools/LLMs
let json = JsonFormatter::pretty().format(&diag);
println!("{}", json);

// Simple language syntax (for specs)
let simple = SimpleFormatter::new().format(&diag);
println!("{}", simple);
```

## Language Selection

### CLI Usage

```bash
# English (default)
simple build main.spl

# Korean
simple build main.spl --lang ko
```

### Programmatic Usage

```rust
// Set locale via environment variable
std::env::set_var("SIMPLE_LANG", "ko");

// Now all diagnostics will use Korean messages
let diag = Diagnostic::error_i18n("parser", "E0002", &ctx);
```

## Error Catalog Format

Error messages are defined in `i18n/*.spl` files:

**English** (`i18n/parser.spl`):
```simple
val messages = {
  "E0002": {
    "id": "E0002",
    "title": "Unexpected Token",
    "message": "unexpected token: expected {expected}, found {found}",
    "label": "expected {expected} here",
    "help": "try adding `{expected}` before this token"
  }
}
```

**Korean** (`i18n/parser.ko.spl`):
```simple
val messages = {
  "E0002": {
    "id": "E0002",
    "title": "예상치 못한 토큰",
    "message": "{expected}을(를) 예상했지만 {found}을(를) 발견했습니다",
    "label": "여기에 {expected}이(가) 필요합니다",
    "help": "이 토큰 앞에 `{expected}`를 추가해 보세요"
  }
}
```

## Context Building

### Simple Context (1-3 values)

```rust
use simple_diagnostics::i18n::{ctx1, ctx2, ctx3};

// One value
let ctx = ctx1("literal", "123abc");

// Two values
let ctx = ctx2("expected", "i32", "found", "bool");

// Three values
let ctx = ctx3("name", "foo", "type", "String", "line", 42);
```

### Complex Context (4+ values)

```rust
use simple_diagnostics::i18n::ContextBuilder;

let ctx = ContextBuilder::new()
    .with("expected", "identifier")
    .with("found", "number")
    .with("line", 42)
    .with("column", 10)
    .build();
```

## Example: Full Workflow

```rust
use simple_parser::Parser;
use simple_driver::convert_parser_diagnostic;
use simple_diagnostics::{TextFormatter, JsonFormatter};

fn compile_and_report(source: &str, use_json: bool) {
    // Parse source code
    let mut parser = Parser::new(source);
    let result = parser.parse();

    // Handle errors
    if let Err(parse_error) = result {
        // Convert parser diagnostic to i18n diagnostic
        let parser_diag = parse_error.to_diagnostic();
        let i18n_diag = convert_parser_diagnostic(parser_diag);

        // Choose formatter based on output mode
        if use_json {
            let formatter = JsonFormatter::pretty();
            let json = formatter.format(&i18n_diag);
            println!("{}", json);
        } else {
            let formatter = TextFormatter::new();
            let text = formatter.format(&i18n_diag, source);
            eprintln!("{}", text);
        }
    }
}

// Example usage
compile_and_report("fn main( { }", false); // Text output
compile_and_report("fn main( { }", true);  // JSON output
```

## Output Examples

### Text Format (Terminal)

```
error[E0002]: unexpected token: expected identifier, found number
  --> test.spl:2:13
   |
 2 |     let x = 42abc
   |             ^^^^^ expected identifier here
   |
   = help: try adding `identifier` before this token
```

### JSON Format (Tools/LLMs)

```json
{
  "severity": "error",
  "code": "E0002",
  "message": "unexpected token: expected identifier, found number",
  "span": {
    "start": 10,
    "end": 15,
    "line": 2,
    "column": 5
  },
  "labels": [
    {
      "span": { "start": 10, "end": 15, "line": 2, "column": 5 },
      "message": "expected identifier here"
    }
  ],
  "help": "try adding `identifier` before this token"
}
```

### Simple Format (Specs)

```simple
Diagnostic(
  severity: Severity.Error,
  code: "E0002",
  message: "unexpected token: expected identifier, found number",
  span: Span(start: 10, end: 15, line: 2, column: 5),
  labels: [
    Label(span: Span(start: 10, end: 15, line: 2, column: 5), message: "expected identifier here"),
  ],
  help: "try adding `identifier` before this token",
)
```

## Testing

### Unit Tests (Module Level)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_diagnostic_creation() {
        let ctx = ctx2("expected", "i32", "found", "bool");
        let diag = Diagnostic::error_i18n("compiler", "E1001", &ctx);

        assert_eq!(diag.code, Some("E1001".to_string()));
        assert!(!diag.message.is_empty());
    }
}
```

### Integration Tests

```rust
#[test]
fn test_end_to_end_diagnostic() {
    std::env::set_var("SIMPLE_LANG", "ko");

    let source = "fn main( { }";
    let mut parser = Parser::new(source);
    let result = parser.parse();

    assert!(result.is_err());
    let diag = convert_parser_diagnostic(result.unwrap_err().to_diagnostic());

    // Korean output
    let formatter = TextFormatter::without_color();
    let output = formatter.format(&diag, source);

    assert!(output.contains("오류")); // "error" in Korean

    std::env::remove_var("SIMPLE_LANG");
}
```

## Performance Considerations

- **Catalog Loading**: Lazy-loaded on first use (~1ms)
- **Message Lookup**: HashMap O(1) lookup - negligible
- **Memory**: ~100KB for en + ko catalogs
- **Runtime**: <0.1ms per diagnostic formatting

## Adding New Languages

1. Create catalog file: `i18n/parser.{lang}.spl`
2. Translate all messages
3. Test with `--lang {lang}`
4. Submit PR with translations

See `doc/contributing/i18n.md` for detailed translation guidelines.

## Troubleshooting

### Issue: Messages Not Localized

**Problem**: Diagnostics show English even with `--lang ko`

**Solution**:
- Verify `SIMPLE_LANG` environment variable is set
- Check catalog files exist in `i18n/`
- Ensure `simple-driver` has `simple-format` feature enabled

### Issue: Missing Message IDs

**Problem**: Error shows generic "Error E0XXX" instead of detailed message

**Solution**:
- Add message to catalog file (`i18n/parser.spl`)
- Rebuild with `cargo build`
- Check error code matches catalog ID

### Issue: Circular Dependency

**Problem**: Cannot add `simple-diagnostics` to parser

**Solution**:
- Parser should NOT depend on `simple-diagnostics`
- Use `simple-common::Diagnostic` in parser
- Convert in driver using `convert_parser_diagnostic()`

## See Also

- **Architecture**: `src/diagnostics/ARCHITECTURE.md`
- **Implementation Status**: `doc/design/diagnostics_implementation_status.md`
- **Integration Plan**: `doc/design/diagnostic_i18n_integration_plan.md`
- **Contributing**: `doc/contributing/i18n.md` (future)
