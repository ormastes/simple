# Unified Diagnostics Crate Plan

**Goal**: Create `src/diagnostics/` crate that consolidates all error reporting, used by both Rust implementation and Simple language.

**Status**: Design Phase
**Approach**: Option 2 - Single unified crate with integrated i18n

---

## Design Principles

1. **Single Source of Truth**: All diagnostic logic in one crate
2. **I18n First**: Localization built-in, not bolted-on
3. **Rust + Simple**: Both implementations use the same system
4. **Zero-cost Default**: English embedded at compile-time
5. **Extensible**: Easy to add new formatters (JSON, HTML, etc.)

---

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│ src/diagnostics/ (NEW unified crate)                       │
│                                                             │
│ ┌─────────────┐ ┌──────────┐ ┌─────────────┐             │
│ │ Diagnostic  │ │ Severity │ │ Span        │             │
│ │ (core type) │ │ (Error,  │ │ (location)  │             │
│ └─────────────┘ │ Warning) │ └─────────────┘             │
│                  └──────────┘                              │
│                                                             │
│ ┌─────────────────────────────────────────────────────┐   │
│ │ I18n Integration (built-in)                         │   │
│ │ - error_i18n() / warning_i18n()                     │   │
│ │ - Localized severity names                          │   │
│ │ - Message interpolation                             │   │
│ └─────────────────────────────────────────────────────┘   │
│                                                             │
│ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐     │
│ │ Text     │ │ JSON     │ │ HTML     │ │ Simple   │     │
│ │ Formatter│ │ Formatter│ │ Formatter│ │ Formatter│     │
│ └──────────┘ └──────────┘ └──────────┘ └──────────┘     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
                          ↑
         ┌────────────────┼────────────────┐
         │                │                │
┌────────────────┐ ┌──────────────┐ ┌──────────────┐
│ Parser         │ │ Compiler     │ │ Runtime      │
│ ParseError     │ │ CompileError │ │ RuntimeError │
│ → Diagnostic   │ │ → Diagnostic │ │ → Diagnostic │
└────────────────┘ └──────────────┘ └──────────────┘
         │                │                │
         └────────────────┼────────────────┘
                          ↓
         ┌────────────────────────────────┐
         │ Driver (displays diagnostics)  │
         │ Uses --lang flag               │
         └────────────────────────────────┘
```

---

## Implementation Plan

### Phase 1: Create Diagnostics Crate

#### 1.1: Create Directory Structure

```bash
mkdir -p src/diagnostics/src/formatters
```

**File structure**:
```
src/diagnostics/
├── Cargo.toml
├── src/
│   ├── lib.rs              # Public API
│   ├── diagnostic.rs       # Diagnostic type (moved from common)
│   ├── severity.rs         # Severity enum
│   ├── span.rs             # Span type
│   ├── i18n.rs             # I18n integration
│   ├── builder.rs          # Diagnostic builder pattern
│   └── formatters/
│       ├── mod.rs          # Formatter trait
│       ├── text.rs         # Text formatter (existing colored output)
│       ├── json.rs         # JSON formatter (for LLM tools)
│       ├── html.rs         # HTML formatter (future)
│       └── simple.rs       # Simple language format (for specs)
```

#### 1.2: Create Cargo.toml

```toml
[package]
name = "simple-diagnostics"
version.workspace = true
edition.workspace = true

[lints]
workspace = true

[dependencies]
# I18n is built-in, not optional
simple_i18n = { path = "../i18n" }

# Serialization for JSON formatter
serde = { workspace = true, features = ["derive"] }
serde_json = { workspace = true }

# Optional: colored output
termcolor = "1.4"

[dev-dependencies]
tempfile = "3.14"
```

### Phase 2: Migrate Diagnostic Code

#### 2.1: Move Core Types

**From**: `src/common/src/diagnostic.rs`
**To**: `src/diagnostics/src/`

**Split into modules**:

**`src/diagnostics/src/span.rs`**:
```rust
/// Source location span (line, column, offset)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
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

    pub fn at(pos: usize, line: usize, column: usize) -> Self {
        Self { start: pos, end: pos, line, column }
    }

    pub fn to(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
            line: self.line.min(other.line),
            column: self.column,
        }
    }
}
```

**`src/diagnostics/src/severity.rs`**:
```rust
use simple_i18n::I18n;

/// Severity level of a diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Error,
    Warning,
    Note,
    Help,
    Info,
}

impl Severity {
    /// Get the English name (for error codes, internal use)
    pub fn name(&self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Note => "note",
            Severity::Help => "help",
            Severity::Info => "info",
        }
    }

    /// Get the localized name for display (i18n-aware)
    pub fn display_name(&self) -> String {
        I18n::global().get_severity(self.name())
    }

    /// Get ANSI color code
    pub fn color(&self) -> &'static str {
        match self {
            Severity::Error => "\x1b[1;31m",   // Bold red
            Severity::Warning => "\x1b[1;33m", // Bold yellow
            Severity::Note => "\x1b[1;36m",    // Bold cyan
            Severity::Help => "\x1b[1;32m",    // Bold green
            Severity::Info => "\x1b[1;34m",    // Bold blue
        }
    }
}
```

#### 2.2: Create I18n-Integrated Diagnostic

**`src/diagnostics/src/diagnostic.rs`**:
```rust
use crate::severity::Severity;
use crate::span::Span;
use simple_i18n::{I18n, MessageContext};
use serde::{Deserialize, Serialize};

/// A diagnostic message (error, warning, note, etc.)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: Option<String>,      // Error code like "E0002"
    pub message: String,
    pub span: Option<Span>,
    pub labels: Vec<DiagnosticLabel>,
    pub notes: Vec<String>,
    pub help: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiagnosticLabel {
    pub span: Span,
    pub message: String,
}

impl Diagnostic {
    // ============================================================
    // Constructor (existing API - backward compatible)
    // ============================================================

    pub fn new(severity: Severity, message: &str) -> Self {
        Self {
            severity,
            code: None,
            message: message.to_string(),
            span: None,
            labels: Vec::new(),
            notes: Vec::new(),
            help: None,
        }
    }

    pub fn error(message: &str) -> Self {
        Self::new(Severity::Error, message)
    }

    pub fn warning(message: &str) -> Self {
        Self::new(Severity::Warning, message)
    }

    // ============================================================
    // I18n Constructors (NEW)
    // ============================================================

    /// Create diagnostic from i18n message ID
    pub fn from_i18n(
        severity: Severity,
        domain: &str,
        id: &str,
        ctx: &MessageContext,
    ) -> Self {
        let i18n = I18n::global();
        let msg = i18n.get_message_safe(domain, id, ctx);

        let mut diag = Self {
            severity,
            code: Some(msg.id.clone()),
            message: msg.message,
            span: None,
            labels: Vec::new(),
            notes: Vec::new(),
            help: msg.help,
        };

        // Add note if present in i18n message
        if let Some(note) = msg.note {
            diag.notes.push(note);
        }

        diag
    }

    /// Create error with i18n
    pub fn error_i18n(domain: &str, id: &str, ctx: &MessageContext) -> Self {
        Self::from_i18n(Severity::Error, domain, id, ctx)
    }

    /// Create warning with i18n
    pub fn warning_i18n(domain: &str, id: &str, ctx: &MessageContext) -> Self {
        Self::from_i18n(Severity::Warning, domain, id, ctx)
    }

    // ============================================================
    // Builder Methods (existing API - backward compatible)
    // ============================================================

    pub fn with_code(mut self, code: &str) -> Self {
        self.code = Some(code.to_string());
        self
    }

    pub fn with_message(mut self, message: &str) -> Self {
        self.message = message.to_string();
        self
    }

    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    pub fn with_label(mut self, span: Span, message: &str) -> Self {
        self.labels.push(DiagnosticLabel {
            span,
            message: message.to_string(),
        });
        self
    }

    /// Add i18n-aware label (NEW)
    pub fn with_label_i18n(mut self, span: Span, domain: &str, id: &str, ctx: &MessageContext) -> Self {
        let i18n = I18n::global();
        let msg = i18n.get_message_safe(domain, id, ctx);

        if let Some(label) = msg.label {
            self.labels.push(DiagnosticLabel {
                span,
                message: label,
            });
        }

        self
    }

    pub fn with_note(mut self, note: &str) -> Self {
        self.notes.push(note.to_string());
        self
    }

    pub fn with_help(mut self, help: &str) -> Self {
        self.help = Some(help.to_string());
        self
    }

    // ============================================================
    // Formatting (delegates to formatters)
    // ============================================================

    /// Format as colored text (default)
    pub fn format(&self, source: &str, use_color: bool) -> String {
        crate::formatters::text::TextFormatter::format(self, source, use_color)
    }

    /// Format as JSON (for LLM tools)
    pub fn format_json(&self, source: &str) -> String {
        crate::formatters::json::JsonFormatter::format(self, source)
    }

    /// Format as Simple language (for specs/docs)
    pub fn format_simple(&self, source: &str) -> String {
        crate::formatters::simple::SimpleFormatter::format(self, source)
    }
}
```

#### 2.3: Create I18n Integration Module

**`src/diagnostics/src/i18n.rs`**:
```rust
//! I18n integration helpers for diagnostics

use simple_i18n::{I18n, MessageContext, InterpolatedMessage};
use crate::diagnostic::Diagnostic;
use crate::severity::Severity;
use crate::span::Span;

/// Helper to create diagnostic with full i18n message
pub fn create_diagnostic_i18n(
    severity: Severity,
    domain: &str,
    id: &str,
    ctx: &MessageContext,
    primary_span: Option<Span>,
) -> Diagnostic {
    let i18n = I18n::global();
    let msg = i18n.get_message_safe(domain, id, ctx);

    let mut diag = Diagnostic::from_i18n(severity, domain, id, ctx);

    // Add primary label if span and label text available
    if let (Some(span), Some(label)) = (primary_span, msg.label) {
        diag = diag.with_label(span, &label);
    }

    diag
}

/// Quick helper for parser errors
pub fn parser_error(id: &str, ctx: &MessageContext, span: Span) -> Diagnostic {
    let i18n = I18n::global();
    let msg = i18n.get_message_safe("parser", id, ctx);

    Diagnostic::error_i18n("parser", id, ctx)
        .with_span(span)
        .with_label(span, msg.label.as_deref().unwrap_or("error here"))
}

/// Quick helper for compiler errors
pub fn compiler_error(id: &str, ctx: &MessageContext, span: Span) -> Diagnostic {
    let i18n = I18n::global();
    let msg = i18n.get_message_safe("compiler", id, ctx);

    Diagnostic::error_i18n("compiler", id, ctx)
        .with_span(span)
        .with_label(span, msg.label.as_deref().unwrap_or("error here"))
}
```

### Phase 3: Create Formatters

#### 3.1: Formatter Trait

**`src/diagnostics/src/formatters/mod.rs`**:
```rust
pub mod text;
pub mod json;
pub mod simple;

use crate::diagnostic::Diagnostic;

/// Trait for diagnostic formatters
pub trait DiagnosticFormatter {
    /// Format a diagnostic with source code context
    fn format(diagnostic: &Diagnostic, source: &str) -> String;
}
```

#### 3.2: Text Formatter (Existing colored output)

**`src/diagnostics/src/formatters/text.rs`**:
```rust
use crate::diagnostic::Diagnostic;
use crate::formatters::DiagnosticFormatter;

pub struct TextFormatter;

impl TextFormatter {
    /// Format with optional color
    pub fn format(diag: &Diagnostic, source: &str, use_color: bool) -> String {
        let mut output = String::new();

        // Use localized severity name
        let severity_name = diag.severity.display_name();  // "error" or "오류" or "エラー"
        let color = if use_color { diag.severity.color() } else { "" };
        let reset = if use_color { "\x1b[0m" } else { "" };

        // Format: error[E0002]: message
        if let Some(code) = &diag.code {
            output.push_str(&format!(
                "{}{}[{}]{}: {}\n",
                color, severity_name, code, reset, diag.message
            ));
        } else {
            output.push_str(&format!(
                "{}{}{}: {}\n",
                color, severity_name, reset, diag.message
            ));
        }

        // Add span location if present
        if let Some(span) = diag.span {
            output.push_str(&format!("  --> {}:{}:{}\n", "<source>", span.line, span.column));
        }

        // Add labels
        for label in &diag.labels {
            output.push_str(&format!("   |\n"));
            output.push_str(&format!("{:>4} | {}\n", label.span.line,
                Self::get_source_line(source, label.span.line)));
            output.push_str(&format!("   | {}{}\n",
                " ".repeat(label.span.column),
                "^".repeat(label.span.end - label.span.start)));
            output.push_str(&format!("   | {}\n", label.message));
        }

        // Add notes
        for note in &diag.notes {
            output.push_str(&format!("   |\n"));
            output.push_str(&format!("   = note: {}\n", note));
        }

        // Add help
        if let Some(help) = &diag.help {
            output.push_str(&format!("   |\n"));
            output.push_str(&format!("   = help: {}\n", help));
        }

        output
    }

    fn get_source_line(source: &str, line: usize) -> &str {
        source.lines().nth(line - 1).unwrap_or("")
    }
}
```

#### 3.3: JSON Formatter (for LLM tools)

**`src/diagnostics/src/formatters/json.rs`**:
```rust
use crate::diagnostic::Diagnostic;
use serde_json;

pub struct JsonFormatter;

impl JsonFormatter {
    pub fn format(diag: &Diagnostic, _source: &str) -> String {
        // Diagnostic already has Serialize derive
        serde_json::to_string_pretty(diag).unwrap_or_else(|_| "{}".to_string())
    }

    pub fn format_compact(diag: &Diagnostic) -> String {
        serde_json::to_string(diag).unwrap_or_else(|_| "{}".to_string())
    }
}
```

#### 3.4: Simple Language Formatter (for specs)

**`src/diagnostics/src/formatters/simple.rs`**:
```rust
use crate::diagnostic::Diagnostic;

pub struct SimpleFormatter;

impl SimpleFormatter {
    /// Format diagnostic as Simple language code (for spec tests)
    pub fn format(diag: &Diagnostic, _source: &str) -> String {
        let mut output = String::new();

        output.push_str("diagnostic {\n");
        output.push_str(&format!("    severity: \"{}\",\n", diag.severity.name()));

        if let Some(code) = &diag.code {
            output.push_str(&format!("    code: \"{}\",\n", code));
        }

        output.push_str(&format!("    message: \"{}\",\n", diag.message));

        if let Some(help) = &diag.help {
            output.push_str(&format!("    help: \"{}\",\n", help));
        }

        output.push_str("}\n");

        output
    }
}
```

### Phase 4: Public API

**`src/diagnostics/src/lib.rs`**:
```rust
//! Unified diagnostic system for Simple language
//!
//! This crate provides:
//! - Error/warning/note reporting
//! - I18n-integrated messages
//! - Multiple formatters (text, JSON, Simple)
//! - Used by both Rust compiler and Simple language

pub mod diagnostic;
pub mod severity;
pub mod span;
pub mod i18n;
pub mod formatters;

// Re-export main types
pub use diagnostic::{Diagnostic, DiagnosticLabel};
pub use severity::Severity;
pub use span::Span;

// Re-export i18n helpers
pub use i18n::{create_diagnostic_i18n, parser_error, compiler_error};

// Re-export MessageContext for convenience
pub use simple_i18n::MessageContext;
```

### Phase 5: Update Dependencies

#### 5.1: Add to Workspace

**`Cargo.toml` (workspace root)**:
```toml
[workspace]
members = [
    "src/common",
    "src/diagnostics",  # NEW
    "src/i18n",
    "src/parser",
    # ...
]
```

#### 5.2: Update Parser

**`src/parser/Cargo.toml`**:
```toml
[dependencies]
simple-diagnostics = { path = "../diagnostics" }  # NEW
# Remove: simple-common for diagnostic types
```

**`src/parser/src/error.rs`**:
```rust
use simple_diagnostics::{Diagnostic, MessageContext, parser_error, Span};

impl ParseError {
    /// Convert to diagnostic (backward compatible)
    pub fn to_diagnostic(&self) -> Diagnostic {
        self.to_diagnostic_i18n()  // Now always uses i18n
    }

    /// Convert to diagnostic with i18n
    pub fn to_diagnostic_i18n(&self) -> Diagnostic {
        match self {
            ParseError::UnexpectedToken { expected, found, span } => {
                let mut ctx = MessageContext::new();
                ctx.insert("expected", expected);
                ctx.insert("found", found);

                parser_error("E0002", &ctx, *span)
            }

            ParseError::MissingToken { expected, span } => {
                let mut ctx = MessageContext::new();
                ctx.insert("expected", expected);

                parser_error("E0010", &ctx, *span)
            }

            // Map all other errors...
        }
    }
}
```

#### 5.3: Update Compiler

**`src/compiler/Cargo.toml`**:
```toml
[dependencies]
simple-diagnostics = { path = "../diagnostics" }  # NEW
```

**`src/compiler/src/error.rs`**:
```rust
use simple_diagnostics::{Diagnostic, MessageContext, compiler_error, Span};

impl CompileError {
    pub fn to_diagnostic(&self) -> Diagnostic {
        match self {
            CompileError::UndefinedVariable { name, span } => {
                let mut ctx = MessageContext::new();
                ctx.insert("name", name);

                compiler_error("E1001", &ctx, *span)
            }

            // Map all compiler errors...
        }
    }
}
```

#### 5.4: Update Driver

**`src/driver/Cargo.toml`**:
```toml
[dependencies]
simple-diagnostics = { path = "../diagnostics" }  # NEW
```

**`src/driver/src/main.rs`**:
```rust
use simple_diagnostics::Diagnostic;

// Diagnostic display already uses i18n automatically
for error in parse_errors {
    let diag = error.to_diagnostic();  // Now i18n-aware by default
    eprintln!("{}", diag.format(&source, true));  // Uses localized severity names
}
```

### Phase 6: Update Common Crate

**`src/common/Cargo.toml`**:
```toml
[dependencies]
simple-diagnostics = { path = "../diagnostics" }  # Re-export for backward compat

# Remove old diagnostic code
```

**`src/common/src/lib.rs`**:
```rust
// Re-export diagnostics for backward compatibility
pub use simple_diagnostics::{Diagnostic, Severity, Span};

// Other common utilities remain
pub mod target;
pub mod source_map;
// ...
```

### Phase 7: Update I18n Catalogs

#### 7.1: Ensure Catalog Structure

**Current structure (already correct)**:
```
i18n/
├── __init__.spl          # English severity names (embedded at build)
├── __init__.ko.spl       # Korean severity names
├── parser.spl            # English parser errors E0001-E0012 (embedded)
├── parser.ko.spl         # Korean parser errors
├── compiler.spl          # English compiler errors (create)
└── compiler.ko.spl       # Korean compiler errors (create)
```

#### 7.2: Create Compiler Error Catalogs

**`i18n/compiler.spl`** (English):
```simple
# English compiler error messages
val messages = {
    "E1001": {
        "id": "E1001",
        "title": "Undefined Variable",
        "message": "cannot find value `{name}` in this scope",
        "label": "`{name}` not found",
        "help": "check if the variable is declared before use"
    },

    "E1002": {
        "id": "E1002",
        "title": "Type Mismatch",
        "message": "expected type `{expected}`, found `{found}`",
        "label": "expected `{expected}`",
        "help": "consider converting the value to the expected type"
    },

    # ... more compiler errors
}
```

**`i18n/compiler.ko.spl`** (Korean):
```simple
# Simple 컴파일러의 한국어 오류 메시지
val messages = {
    "E1001": {
        "id": "E1001",
        "title": "정의되지 않은 변수",
        "message": "이 범위에서 값 `{name}`을(를) 찾을 수 없습니다",
        "label": "`{name}`을(를) 찾을 수 없음",
        "help": "변수가 사용 전에 선언되었는지 확인하세요"
    },

    "E1002": {
        "id": "E1002",
        "title": "타입 불일치",
        "message": "타입 `{expected}`을(를) 예상했지만 `{found}`을(를) 발견했습니다",
        "label": "`{expected}` 타입 필요",
        "help": "값을 예상된 타입으로 변환하는 것을 고려하세요"
    },

    # ... 더 많은 컴파일러 오류
}
```

---

## Simple Language Integration

### Simple Error Specs (BDD Tests)

**`simple/std_lib/test/features/diagnostics/error_reporting.spl`**:
```simple
# BDD spec for error reporting
feature "Error Reporting":
    scenario "Show localized error messages":
        given:
            val code = """
                fn main(
                    return 0
            """

        when:
            val result = compile(code, lang: "ko")

        then:
            result.has_error("E0010")
            result.error_message.contains("필요한 토큰이 누락되었습니다")
            result.error_label.contains("여기에")

    scenario "Fallback to English":
        given:
            val code = "fn main("

        when:
            val result = compile(code, lang: "unknown")

        then:
            result.has_error("E0010")
            result.error_message.contains("missing expected token")

    scenario "JSON format for LLM tools":
        given:
            val code = "fn main("

        when:
            val json = compile(code, format: "json")

        then:
            json.severity == "error"
            json.code == "E0010"
            json.has_field("span")
            json.has_field("labels")
```

### Simple Diagnostic API

**Future: Simple language can create diagnostics**:
```simple
# In Simple stdlib (future)
import diagnostics::{Diagnostic, Severity}

fn report_custom_error(message: String, span: Span):
    val diag = Diagnostic.error_i18n(
        domain: "custom",
        id: "C0001",
        context: { "message": message }
    )
    diag.with_span(span)
    diag.with_help("Check your custom logic")

    diag.display()
```

---

## Migration Checklist

### Phase 1: Create Diagnostics Crate
- [ ] Create `src/diagnostics/` directory structure
- [ ] Create `Cargo.toml` with simple_i18n dependency
- [ ] Move `Span` from common to diagnostics
- [ ] Move `Severity` from common to diagnostics
- [ ] Move `Diagnostic` from common to diagnostics
- [ ] Add i18n integration to Severity::display_name()
- [ ] Add i18n constructors to Diagnostic

### Phase 2: Create Formatters
- [ ] Create `formatters/mod.rs` with trait
- [ ] Implement `formatters/text.rs` (existing colored output)
- [ ] Implement `formatters/json.rs` (for LLM tools)
- [ ] Implement `formatters/simple.rs` (for specs)
- [ ] Test all formatters

### Phase 3: Update Dependencies
- [ ] Add diagnostics to workspace members
- [ ] Update `src/parser/` to use simple-diagnostics
- [ ] Update `src/compiler/` to use simple-diagnostics
- [ ] Update `src/driver/` to use simple-diagnostics
- [ ] Update `src/common/` to re-export for backward compat
- [ ] Remove old diagnostic code from common

### Phase 4: Update Error Implementations
- [ ] Update `ParseError::to_diagnostic()` to use i18n
- [ ] Map all parser errors (E0001-E0012) to i18n IDs
- [ ] Update `CompileError::to_diagnostic()` to use i18n
- [ ] Map compiler errors to i18n IDs
- [ ] Test all error paths

### Phase 5: Create Compiler Catalogs
- [ ] Create `i18n/compiler.spl` (English)
- [ ] Create `i18n/compiler.ko.spl` (Korean)
- [ ] Update build.rs to include compiler catalogs
- [ ] Test compiler error localization

### Phase 6: Testing
- [ ] Unit tests for each formatter
- [ ] Integration tests for i18n diagnostics
- [ ] Test Korean error output end-to-end
- [ ] Test JSON formatter
- [ ] Test fallback chain
- [ ] Run `make check`

### Phase 7: Documentation
- [ ] Update `doc/guide/i18n.md` with new API
- [ ] Document formatter usage
- [ ] Add examples for each formatter
- [ ] Update architecture docs
- [ ] Create Simple language diagnostic API spec

---

## Benefits

### ✅ Single Source of Truth
- All diagnostic logic in one place
- No duplication between crates
- Easier to maintain and extend

### ✅ I18n Built-in
- Localization is the default, not optional
- Severity names automatically localized
- Full message interpolation support

### ✅ Multiple Formatters
- Text (colored terminal output)
- JSON (for LLM tools, IDE integration)
- Simple language (for specs/tests)
- Easy to add HTML, Markdown, etc.

### ✅ Rust + Simple Integration
- Same diagnostic system for both
- Simple specs can test error messages
- Consistent behavior across implementations

### ✅ Extensible
- Easy to add new error codes
- Easy to add new formatters
- Easy to add new languages

---

## Timeline

| Phase | Duration | Priority |
|-------|----------|----------|
| Phase 1: Create crate | 2 hours | High |
| Phase 2: Formatters | 2 hours | High |
| Phase 3: Update deps | 1 hour | High |
| Phase 4: Update errors | 3 hours | High |
| Phase 5: Compiler catalogs | 1 hour | Medium |
| Phase 6: Testing | 2 hours | High |
| Phase 7: Documentation | 1 hour | Medium |
| **Total** | **~12 hours** | |

---

## Success Criteria

- [ ] All tests pass (no regressions)
- [ ] Korean error messages display correctly
- [ ] JSON formatter works for LLM tools
- [ ] Simple specs can test diagnostics
- [ ] No circular dependencies
- [ ] Performance unchanged
- [ ] Documentation complete

---

## Next Steps

1. Create `src/diagnostics/` directory structure
2. Move Span, Severity, Diagnostic from common
3. Integrate i18n into Diagnostic
4. Create formatters
5. Update all dependent crates
6. Test end-to-end

Ready to implement?
