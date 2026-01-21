# Diagnostics System Architecture

## Overview

The Simple compiler uses a **layered diagnostic architecture** to provide rich, localized error messages while avoiding circular dependencies.

## Architecture Layers

```
┌─────────────────────────────────────────────┐
│          Driver / Compiler (Top Layer)      │
│                                              │
│  Uses: simple-diagnostics (full-featured)   │
│  - Localized messages (via i18n)            │
│  - Multiple formatters (text, JSON, Simple) │
│  - Rich error context                       │
└──────────────────┬──────────────────────────┘
                   │
                   │ Converts errors
                   ▼
┌──────────────────────────────────────────────┐
│           Parser (Bottom Layer)              │
│                                               │
│  Uses: simple-common::Diagnostic (minimal)   │
│  - No i18n dependency                        │
│  - Lightweight, core functionality           │
│  - No circular dependencies                  │
└───────────────────────────────────────────────┘
```

## Why This Design?

### The Circular Dependency Problem

We initially wanted the parser to use `simple-diagnostics` directly, but this creates a circular dependency:

```
Parser → Diagnostics → I18n → Parser (to parse .spl catalogs)
```

This cycle cannot be broken while maintaining:
- I18n support in diagnostics
- `.spl` format for i18n catalogs (requires parser)
- Direct diagnostics usage in parser

### The Solution: Layered Architecture

**Bottom Layer (Parser)**:
- Uses minimal `simple-common::Diagnostic`
- No i18n, no complex formatting
- Lightweight and dependency-free
- Reports errors with spans and messages

**Top Layer (Driver/Compiler)**:
- Uses full-featured `simple-diagnostics`
- Converts parser errors to localized diagnostics
- Applies formatters for output
- Handles all user-facing error display

## Usage Guide

### For Parser Authors

Use the minimal diagnostic from `simple-common`:

```rust
use simple_common::{Diagnostic, Severity, Span};

fn report_error() -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: Some("E0001".to_string()),
        message: "unexpected token".to_string(),  // English only
        span: Some(Span::new(0, 5, 1, 1)),
        labels: vec![],
        notes: vec![],
        help: None,
    }
}
```

### For Driver/Compiler Authors

Convert parser diagnostics to i18n-aware diagnostics:

```rust
use simple_diagnostics::{Diagnostic as I18nDiagnostic, i18n::ctx2};

fn convert_parser_error(parser_diag: simple_common::Diagnostic) -> I18nDiagnostic {
    match parser_diag.code.as_deref() {
        Some("E0002") => {
            // Extract context from parser diagnostic
            let ctx = ctx2("expected", "identifier", "found", "number");

            I18nDiagnostic::error_i18n("parser", "E0002", &ctx)
                .with_span(parser_diag.span.unwrap())
        },
        _ => {
            // Fallback: use parser message as-is
            I18nDiagnostic::error(parser_diag.message)
                .with_code(parser_diag.code.unwrap_or_default())
                .with_span(parser_diag.span.unwrap_or(Span::at(0, 0, 0)))
        }
    }
}
```

### Output Formatting

The driver chooses the appropriate formatter:

```rust
use simple_diagnostics::{TextFormatter, JsonFormatter};

// Terminal output (colored)
let formatter = TextFormatter::new();
let output = formatter.format(&diagnostic, source_code);
eprintln!("{}", output);

// JSON output for tools
let formatter = JsonFormatter::pretty();
let json = formatter.format(&diagnostic);
println!("{}", json);
```

## Benefits of This Architecture

1. **No Circular Dependencies**: Parser remains lightweight
2. **Full I18n Support**: Driver gets localized messages
3. **Separation of Concerns**: Parsing vs. presentation are decoupled
4. **Flexibility**: Can add new formatters without changing parser
5. **Performance**: Parser doesn't pay for i18n overhead

## Error Catalog Structure

Error message catalogs are organized by domain:

```
i18n/
├── __init__.spl          # Common UI strings (English)
├── __init__.ko.spl       # Common UI strings (Korean)
├── parser.spl            # Parser errors (English)
├── parser.ko.spl         # Parser errors (Korean)
├── compiler.spl          # Compiler errors (English)
└── compiler.ko.spl       # Compiler errors (Korean)
```

Example catalog entry (`parser.spl`):

```simple
val messages = {
  "E0002": {
    id: "E0002",
    title: "Unexpected Token",
    message: "unexpected token: expected {expected}, found {found}",
    label: "expected {expected} here",
    help: "try adding `{expected}` before this token"
  }
}
```

## Migration Path

Current state (**Phase 1-3 complete**):
- ✅ Created `simple-diagnostics` crate with i18n support
- ✅ Implemented formatters (text, JSON, Simple)
- ✅ Resolved circular dependency (parser uses minimal diagnostics)

Next steps:
- ⏳ Create error message catalogs (English, Korean)
- ⏳ Create conversion helpers in driver
- ⏳ Update compiler to use diagnostics
- ⏳ Full integration testing

## Future Enhancements

- **Additional Languages**: Japanese, Chinese, Spanish
- **LSP Integration**: Send localized diagnostics to IDEs
- **HTML Formatter**: For documentation and web tools
- **Severity Filtering**: Control which diagnostics are shown
