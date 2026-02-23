# Diagnostic I18n Integration Plan

**Status**: Design Phase
**Goal**: Integrate i18n with existing diagnostic system without major refactoring

---

## Current Architecture

```
src/common/
  └── diagnostic.rs         # Diagnostic, Severity, Span

src/parser/
  └── error.rs              # ParseError → to_diagnostic()

src/compiler/
  └── error.rs              # CompileError → to_diagnostic()

src/src/i18n/                   # NEW - i18n system
  ├── catalog.rs
  ├── message.rs
  └── lib.rs
```

---

## Proposed Integration

### Step 1: Add I18n Helpers to Diagnostic (src/common/)

**Add dependency to common/Cargo.toml**:
```toml
[dependencies]
simple_i18n = { path = "../i18n", optional = true }

[features]
i18n = ["dep:simple_i18n"]
```

**Add helper methods to diagnostic.rs**:
```rust
#[cfg(feature = "i18n")]
use simple_i18n::{I18n, MessageContext, InterpolatedMessage};

impl Diagnostic {
    /// Create diagnostic from i18n message ID
    #[cfg(feature = "i18n")]
    pub fn from_i18n_message(
        severity: Severity,
        domain: &str,
        id: &str,
        ctx: &MessageContext,
        span: Span,
    ) -> Self {
        let i18n = I18n::global();

        // Get localized message (with fallback to bootstrap)
        let msg = i18n.get_message_safe(domain, id, ctx);

        let mut diag = Diagnostic::new(severity, id)
            .with_message(&msg.message)
            .with_span(span);

        if let Some(label) = msg.label {
            diag = diag.with_label(span, &label);
        }

        if let Some(help) = msg.help {
            diag = diag.with_help(&help);
        }

        if let Some(note) = msg.note {
            diag = diag.with_note(&note);
        }

        diag
    }

    /// Shorthand for error with i18n
    #[cfg(feature = "i18n")]
    pub fn error_i18n(
        domain: &str,
        id: &str,
        ctx: &MessageContext,
        span: Span,
    ) -> Self {
        Self::from_i18n_message(Severity::Error, domain, id, ctx, span)
    }

    /// Shorthand for warning with i18n
    #[cfg(feature = "i18n")]
    pub fn warning_i18n(
        domain: &str,
        id: &str,
        ctx: &MessageContext,
        span: Span,
    ) -> Self {
        Self::from_i18n_message(Severity::Warning, domain, id, ctx, span)
    }
}

impl Severity {
    /// Get localized severity name
    #[cfg(feature = "i18n")]
    pub fn name_localized(&self) -> String {
        I18n::global().get_severity(self.name())
    }

    #[cfg(not(feature = "i18n"))]
    pub fn name_localized(&self) -> &'static str {
        self.name()
    }
}
```

### Step 2: Update Parser Errors (src/parser/error.rs)

**Add i18n-aware method**:
```rust
impl ParseError {
    /// Convert to diagnostic (existing method - unchanged for backward compat)
    pub fn to_diagnostic(&self) -> Diagnostic {
        // Existing implementation remains
        match self {
            ParseError::UnexpectedToken { expected, found, span } => {
                Diagnostic::error("E0002")
                    .with_message(&format!("unexpected token: expected {}, found {}", expected, found))
                    .with_span(*span)
                    .with_label(*span, &format!("expected {} here", expected))
            }
            // ...
        }
    }

    /// Convert to localized diagnostic (NEW)
    #[cfg(feature = "i18n")]
    pub fn to_diagnostic_i18n(&self) -> Diagnostic {
        match self {
            ParseError::UnexpectedToken { expected, found, span } => {
                let mut ctx = MessageContext::new();
                ctx.insert("expected", expected);
                ctx.insert("found", found);

                Diagnostic::error_i18n("parser", "E0002", &ctx, *span)
            }

            ParseError::MissingToken { expected, span } => {
                let mut ctx = MessageContext::new();
                ctx.insert("expected", expected);

                Diagnostic::error_i18n("parser", "E0010", &ctx, *span)
            }

            // ... map all other errors to their i18n IDs
        }
    }
}
```

### Step 3: Update Diagnostic Display to Use I18n

**Update display logic to use localized severity**:
```rust
impl Diagnostic {
    pub fn format(&self, source: &str, use_color: bool) -> String {
        let mut output = String::new();

        // Use localized severity name
        let severity_name = self.severity.name_localized();
        let color = if use_color { self.severity.color() } else { "" };

        output.push_str(&format!(
            "{}{}{}: {}",
            color,
            severity_name,  // "error" or "오류" or "エラー"
            if use_color { "\x1b[0m" } else { "" },
            self.message
        ));

        // ... rest of formatting
    }
}
```

### Step 4: Update Driver to Use I18n Diagnostics

**In driver, enable i18n feature and use new methods**:
```rust
// In src/driver/Cargo.toml
[dependencies]
simple-common = { path = "../common", features = ["i18n"] }

// In driver code
let errors = parser.parse_errors();
for error in errors {
    #[cfg(feature = "i18n")]
    let diagnostic = error.to_diagnostic_i18n();

    #[cfg(not(feature = "i18n"))]
    let diagnostic = error.to_diagnostic();

    eprintln!("{}", diagnostic.format(source, true));
}
```

---

## Migration Strategy

### Phase 1: Foundation (Optional i18n)
- [ ] Add i18n feature to common crate
- [ ] Add helper methods to Diagnostic
- [ ] Add `name_localized()` to Severity
- [ ] Make i18n optional (backward compatible)

### Phase 2: Parser Integration
- [ ] Add `to_diagnostic_i18n()` to ParseError
- [ ] Map all ParseError variants to i18n message IDs
- [ ] Test with `--lang ko`
- [ ] Keep `to_diagnostic()` for backward compat

### Phase 3: Compiler Integration
- [ ] Add `to_diagnostic_i18n()` to CompileError
- [ ] Create compiler error catalogs (src/i18n/compiler.spl)
- [ ] Translate to Korean

### Phase 4: Runtime Integration
- [ ] Add runtime error catalogs
- [ ] Integrate with FFI error reporting

### Phase 5: Driver Adoption
- [ ] Enable i18n feature in driver
- [ ] Use `to_diagnostic_i18n()` everywhere
- [ ] Remove old `to_diagnostic()` calls
- [ ] Test full pipeline

---

## Backward Compatibility

**Old code continues to work**:
```rust
// Old API - still works
let diag = ParseError::UnexpectedToken { ... }.to_diagnostic();

// New API - optional
#[cfg(feature = "i18n")]
let diag = error.to_diagnostic_i18n();
```

**Feature flags**:
```bash
# Without i18n (existing behavior)
cargo build

# With i18n (new localized behavior)
cargo build --features i18n
```

---

## Testing Strategy

### Unit Tests
```rust
#[cfg(feature = "i18n")]
#[test]
fn test_diagnostic_i18n() {
    std::env::set_var("SIMPLE_LANG", "ko");

    let mut ctx = MessageContext::new();
    ctx.insert("expected", "식별자");
    ctx.insert("found", "숫자");

    let diag = Diagnostic::error_i18n("parser", "E0002", &ctx, span);
    assert!(diag.message.contains("식별자"));
    assert!(diag.message.contains("숫자"));
}
```

### Integration Tests
```bash
# Test Korean output
simple build test_error.spl --lang ko
# Should see: 오류[E0002]: ...

# Test English (default)
simple build test_error.spl
# Should see: error[E0002]: ...
```

---

## Alternative: Single Unified Crate

**If you prefer consolidation**, create `src/diagnostics/`:

```
src/diagnostics/
├── Cargo.toml
├── src/
│   ├── lib.rs           # Re-export everything
│   ├── diagnostic.rs    # Diagnostic type (moved from common)
│   ├── severity.rs      # Severity enum
│   ├── span.rs          # Span type
│   ├── i18n.rs          # I18n integration
│   └── formatters/
│       ├── text.rs      # Text formatter
│       ├── json.rs      # JSON formatter
│       └── html.rs      # HTML formatter (future)
```

**Then**:
- Move diagnostic code from `src/common/` to `src/diagnostics/`
- Integrate i18n directly
- All domains depend on `simple-diagnostics`

**Pros**:
- Single source of truth
- Cleaner i18n integration
- Easier to add new formatters

**Cons**:
- More refactoring required
- Breaks existing imports
- Need to update all crates

---

## Recommendation

**Start with Option 1 (Distributed + I18n Helpers)**:
1. Less disruptive
2. Backward compatible
3. Can consolidate later if needed
4. Gradual migration path

**Future consideration**: If diagnostic code grows significantly, consider extracting to `src/diagnostics/` crate.

---

## Questions?

- Should we make i18n mandatory or optional (feature flag)?
- Should we migrate all errors at once or gradually?
- Do we want HTML/JSON formatters in the future?
