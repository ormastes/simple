# I18n Rust Compiler Integration Plan

## Overview

Complete plan to make Rust compiler work with Simple language `__init__` i18n files, including documentation updates, architecture design, and phased implementation.

---

## Current State

### Existing Files
```
i18n/
├── __init__.spl           ✅ English common UI (severity names)
├── __init__.ko.spl        ✅ Korean common UI
├── parser.spl             ✅ English parser errors (E0001-E0012)
└── parser.ko.spl          ✅ Korean parser errors
```

### Partial Implementation
```
src/i18n/
├── src/
│   ├── lib.rs             ✅ I18n global singleton
│   ├── locale.rs          ✅ Locale detection
│   ├── message.rs         ✅ Message interpolation
│   ├── catalog.rs         ⚠️  Needs refactor for locale suffix
│   ├── simple_catalog.rs  ⚠️  Needs refactor for locale suffix
│   ├── bootstrap.rs       ✅ Fallback messages
│   └── error.rs           ✅ Error types
└── Cargo.toml             ⚠️  Needs phf dependencies
```

### What's Missing
- ❌ Build-time catalog compilation
- ❌ Locale suffix support (`__init__.ko.spl`)
- ❌ Fallback chain (ko → en)
- ❌ Integration with parser/compiler errors
- ❌ CLI `--lang` flag

---

## Architecture Overview

### Three-Layer System

```
┌─────────────────────────────────────────────────────────┐
│  Layer 1: Build-Time (Compile Default Locale)          │
│  - Parse i18n/__init__.spl at cargo build time         │
│  - Generate Rust const/static data structures          │
│  - Embed in binary (zero runtime cost)                 │
└─────────────────────────────────────────────────────────┘
                          ↓
┌─────────────────────────────────────────────────────────┐
│  Layer 2: Runtime Catalog Loading                      │
│  - Detect requested locale from env/CLI                │
│  - Load __init__.<locale>.spl if non-default           │
│  - Parse and cache in memory                           │
└─────────────────────────────────────────────────────────┘
                          ↓
┌─────────────────────────────────────────────────────────┐
│  Layer 3: Message Retrieval with Fallback              │
│  - Try requested locale first                          │
│  - Fall back to embedded default if missing            │
│  - Interpolate placeholders                            │
└─────────────────────────────────────────────────────────┘
```

### Data Flow

```
Compile Time (build.rs)
  ├─ Parse i18n/__init__.spl
  ├─ Extract val severity = {...}
  ├─ Generate Rust code:
  │    pub const DEFAULT_SEVERITY: phf::Map<&str, &str> = ...
  └─ Embed in binary

Runtime (--lang ko)
  ├─ I18n::from_env() detects locale="ko"
  ├─ Check if locale.is_default() → false
  ├─ Load i18n/__init__.ko.spl
  │    ├─ Parse Simple code
  │    ├─ Extract val severity
  │    └─ Store in HashMap
  ├─ Get message: i18n.get("error")
  │    ├─ Try Korean catalog → "오류"
  │    └─ Return
  └─ Get message: i18n.get("nonexistent")
       ├─ Try Korean catalog → not found
       ├─ Fall back to DEFAULT_SEVERITY → "nonexistent"
       └─ Return fallback

Runtime (default)
  ├─ I18n::from_env() detects locale="en" (or unset)
  ├─ Check if locale.is_default() → true
  ├─ Use DEFAULT_SEVERITY directly (no I/O)
  ├─ Get message: i18n.get("error")
  │    └─ Return DEFAULT_SEVERITY["error"] → "error"
  └─ Zero overhead - compile-time constant
```

---

## Documentation Plan

### New Documents to Create

#### 1. User Guide: `doc/guide/i18n.md`
```markdown
# Internationalization (I18n) in Simple

## Overview
Simple compiler supports multiple languages for error messages.

## Using Localized Errors

### Environment Variable
export SIMPLE_LANG=ko
simple build main.spl
# Errors in Korean: 오류[E0002]: ...

### Command Line Flag
simple build main.spl --lang ko

### Default Behavior
# Without --lang, uses system locale (LANG env var)
# Falls back to English if locale not supported

## Supported Languages
- English (en) - default, embedded in compiler
- Korean (ko) - loaded at runtime
- Japanese (ja) - coming soon

## Adding New Translations
See doc/contributing/i18n_translation.md
```

#### 2. Contributor Guide: `doc/contributing/i18n_translation.md`
```markdown
# Adding I18n Translations

## File Structure
i18n/
├── __init__.spl          # English (default)
├── __init__.<locale>.spl # Your language
├── parser.spl            # English parser errors
└── parser.<locale>.spl   # Your language parser errors

## Adding Korean Translation

1. Create files:
   - i18n/__init__.ko.spl
   - i18n/parser.ko.spl
   - i18n/compiler.ko.spl (if needed)

2. Copy English template:
   cp i18n/__init__.spl i18n/__init__.ko.spl

3. Translate content:
   val severity = {
       "error": "오류",      # Translate to Korean
       "warning": "경고",
       ...
   }

4. Test:
   simple build test.spl --lang ko

## Translation Guidelines
- Keep {placeholder} syntax unchanged
- Match error code structure
- Use formal/polite tone
- Test with actual error cases
```

#### 3. Technical Spec: `doc/spec/i18n_architecture.md`
```markdown
# I18n Architecture Specification

## File Naming Convention

Pattern: `<basename>.<locale>.spl`

- Default (no locale): `__init__.spl`, `parser.spl`
- Locale-specific: `__init__.ko.spl`, `parser.ja.spl`

## Locale Resolution

Locale codes follow ISO 639-1 (2-letter) or BCP 47:
- ko, ja, zh, fr, de, es, ru, ar
- ko_KR, zh_CN, zh_TW (with region)

Fallback chain:
1. Full locale (ko_KR)
2. Language only (ko)
3. Default (en)

## Build-Time Embedding

Default locale compiled into binary:
- Zero runtime cost for default
- ~10KB binary size increase
- Perfect hash maps (phf crate)

## Runtime Loading

Non-default locales loaded on-demand:
- Parse .spl file (~1-2ms)
- Cache in memory
- Subsequent access: O(1)

## File Format

Content: Simple language code
- Variables: `val severity = {...}`
- Functions: `fn format_error_count(...)`
- No module system features
```

### Documents to Update

#### 1. Update `CLAUDE.md`
```markdown
## I18n System

Error messages support multiple languages:
- **Default**: English (embedded in compiler)
- **Runtime**: Korean, Japanese (loaded on-demand)

**Files**: `i18n/__init__.spl`, `i18n/__init__.ko.spl`

**Usage**:
simple build main.spl --lang ko   # Korean errors

**Adding translations**: See `doc/contributing/i18n_translation.md`
```

#### 2. Update `README.md`
```markdown
## Features

- ...
- **Internationalized Error Messages**: Compiler errors in multiple languages
  - English (default, zero-cost)
  - Korean
  - Japanese (coming soon)
```

#### 3. Update `doc/architecture/overview.md`
```markdown
## I18n Subsystem

Location: `src/i18n/`, `i18n/*.spl`

**Purpose**: Multi-language error messages

**Architecture**:
- Build-time: Default locale compiled in
- Runtime: Other locales loaded on-demand
- Fallback: Always falls back to English

**Files**:
- `i18n/__init__.spl` - Common UI strings (English)
- `i18n/__init__.ko.spl` - Korean UI strings
- `i18n/parser.spl` - Parser errors (English)
- `i18n/parser.ko.spl` - Korean parser errors
```

---

## Implementation Plan

### Phase 1: Locale Suffix Support (Foundation)

**Goal**: Make Rust recognize `__init__.ko.spl` pattern

**Files to modify**:
1. `src/i18n/src/catalog.rs`
2. `src/i18n/src/simple_catalog.rs`

**Changes**:

```rust
// src/i18n/src/catalog.rs

impl CatalogRegistry {
    /// Load a catalog with locale suffix support
    ///
    /// For default locale (en):
    ///   common → i18n/__init__.spl
    ///   parser → i18n/parser.spl
    ///
    /// For other locales (ko):
    ///   common → i18n/__init__.ko.spl
    ///   parser → i18n/parser.ko.spl
    pub fn load(&mut self, locale: &str, domain: &str) -> Result<()> {
        let catalog_dir = self.catalog_dir.as_ref()
            .ok_or_else(|| I18nError::CatalogDirectoryNotFound("not set".to_string()))?;

        // Determine filename based on locale and domain
        let filename = if locale == "en" || locale.is_empty() {
            // Default locale - no suffix
            if domain == "common" {
                "__init__.spl".to_string()
            } else {
                format!("{}.spl", domain)
            }
        } else {
            // Non-default locale - add locale suffix
            if domain == "common" {
                format!("__init__.{}.spl", locale)
            } else {
                format!("{}.{}.spl", domain, locale)
            }
        };

        let path = catalog_dir.join(&filename);

        // If locale-specific file doesn't exist, try fallback
        if !path.exists() && locale != "en" {
            // Fall back to default (English)
            return self.load("en", domain);
        }

        if !path.exists() {
            return Err(I18nError::CatalogLoadError {
                path: path.display().to_string(),
                source: std::io::Error::new(
                    std::io::ErrorKind::NotFound,
                    format!("Catalog file not found: {}", filename),
                ),
            });
        }

        let catalog = SimpleCatalogParser::parse_catalog(&path, domain, locale)?;
        self.register(catalog);
        Ok(())
    }

    /// Get message with automatic fallback
    pub fn get_message_with_fallback(
        &self,
        locale: &Locale,
        domain: &str,
        id: &str,
    ) -> Option<&LocalizedMessage> {
        // Try requested locale
        if let Some(catalog) = self.get(locale.language_code(), domain) {
            if let Some(msg) = catalog.get(id) {
                return Some(msg);
            }
        }

        // Fall back to English
        if locale.language_code() != "en" {
            if let Some(catalog) = self.get("en", domain) {
                if let Some(msg) = catalog.get(id) {
                    return Some(msg);
                }
            }
        }

        None
    }
}
```

**Tests**:
```rust
#[test]
fn test_locale_suffix_loading() {
    let mut registry = CatalogRegistry::new()
        .with_catalog_dir("i18n");

    // Load Korean
    registry.load("ko", "common").unwrap();

    let ko_catalog = registry.get("ko", "common").unwrap();
    assert_eq!(ko_catalog.locale, "ko");

    let severity = ko_catalog.get("error").unwrap();
    assert_eq!(severity.message, "오류");
}

#[test]
fn test_fallback_to_english() {
    let mut registry = CatalogRegistry::new()
        .with_catalog_dir("i18n");

    // Load non-existent Japanese -> falls back to English
    registry.load("ja", "common").unwrap();

    let catalog = registry.get("en", "common").unwrap();
    assert_eq!(catalog.locale, "en");
}
```

### Phase 2: Build-Time Catalog Compilation (Performance)

**Goal**: Embed default locale at compile time for zero-cost access

**New files**:
1. `src/i18n/build.rs` - Build script
2. `src/i18n/src/codegen/` - Code generation utilities

**Add dependencies** to `src/i18n/Cargo.toml`:
```toml
[dependencies]
phf = "0.11"

[build-dependencies]
phf_codegen = "0.11"
simple-parser = { path = "../parser" }
```

**Create `src/i18n/build.rs`**:
```rust
use phf_codegen::Map;
use simple_parser::Parser;
use std::env;
use std::fs::{self, File};
use std::io::{BufWriter, Write};
use std::path::Path;

fn main() {
    println!("cargo:rerun-if-changed=../../i18n");

    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("default_catalogs.rs");
    let mut file = BufWriter::new(File::create(&dest_path).unwrap());

    // Generate DEFAULT_SEVERITY
    generate_severity_map(&mut file);

    // Generate DEFAULT_PARSER_MESSAGES
    generate_parser_messages(&mut file);
}

fn generate_severity_map<W: Write>(file: &mut W) {
    // Parse i18n/__init__.spl
    let content = fs::read_to_string("../../i18n/__init__.spl")
        .expect("Failed to read i18n/__init__.spl");

    let mut parser = Parser::new(&content);
    let ast = parser.parse().expect("Failed to parse __init__.spl");

    // Extract val severity = {...}
    let severity_dict = extract_variable(&ast, "severity")
        .expect("No 'severity' variable found in __init__.spl");

    // Generate phf::Map
    writeln!(file, "pub static DEFAULT_SEVERITY: phf::Map<&'static str, &'static str> = \\").unwrap();

    let mut map = Map::new();
    for (key, value) in severity_dict {
        map.entry(&key, &format!("\"{}\"", value));
    }

    writeln!(file, "{};", map.build()).unwrap();
    writeln!(file).unwrap();
}

fn generate_parser_messages<W: Write>(file: &mut W) {
    // Similar to generate_severity_map
    // Parse i18n/parser.spl
    // Extract val messages = {...}
    // Generate phf::Map<&str, LocalizedMessage>

    let content = fs::read_to_string("../../i18n/parser.spl")
        .expect("Failed to read i18n/parser.spl");

    // ... parse and extract ...

    writeln!(file, "pub static DEFAULT_PARSER_MESSAGES: phf::Map<&'static str, LocalizedMessage> = ...").unwrap();
}

fn extract_variable(ast: &Module, name: &str) -> Option<Vec<(String, String)>> {
    // Walk AST to find `val <name> = {...}`
    // Extract dictionary literal
    // Return as Vec of key-value pairs
    todo!("Implement AST walking")
}
```

**Update `src/i18n/src/lib.rs`**:
```rust
// Include generated code
include!(concat!(env!("OUT_DIR"), "/default_catalogs.rs"));

impl I18n {
    pub fn with_default_locale() -> Self {
        Self {
            locale: Locale::default(),
            registry: SharedCatalogRegistry::from_defaults(),
        }
    }
}

impl SharedCatalogRegistry {
    /// Create registry with compile-time embedded defaults
    pub fn from_defaults() -> Self {
        let mut registry = CatalogRegistry::new();

        // Load from generated constants
        let mut catalog = MessageCatalog {
            version: "1.0".to_string(),
            locale: "en".to_string(),
            domain: "common".to_string(),
            messages: HashMap::new(),
        };

        // Convert phf::Map to HashMap
        for (key, value) in DEFAULT_SEVERITY.entries() {
            catalog.messages.insert(
                (*key).to_string(),
                LocalizedMessage {
                    id: (*key).to_string(),
                    title: value.to_string(),
                    message: value.to_string(),
                    label: None,
                    help: None,
                    note: None,
                },
            );
        }

        registry.register(catalog);
        Self::new(registry)
    }
}
```

### Phase 3: Parser/Compiler Integration

**Goal**: Use i18n in actual error reporting

**Files to modify**:
1. `src/parser/src/error.rs`
2. `src/compiler/src/error.rs`
3. `src/driver/src/main.rs`

**Update `src/parser/src/error.rs`**:
```rust
use simple_i18n::{I18n, MessageContext};

impl ParseError {
    /// Convert to diagnostic with i18n support
    pub fn to_diagnostic_i18n(&self, i18n: &I18n) -> Diagnostic {
        match self {
            ParseError::UnexpectedToken { expected, found, span } => {
                let mut ctx = MessageContext::new();
                ctx.insert("expected", expected);
                ctx.insert("found", found);

                // Try to get localized message
                if let Some(msg) = i18n.get_message("parser", "E0002", &ctx) {
                    return Diagnostic::error(msg.message)
                        .with_code(msg.id)
                        .with_parser_label(*span, msg.label.unwrap_or_default())
                        .with_help_opt(msg.help);
                }

                // Fallback to English (from bootstrap or default)
                Diagnostic::error(format!("unexpected token: expected {}, found {}", expected, found))
                    .with_code("E0002")
                    .with_parser_label(*span, format!("expected {} here", expected))
            }
            // ... other error types
        }
    }

    /// Backward compatible - uses global i18n
    pub fn to_diagnostic(&self) -> Diagnostic {
        self.to_diagnostic_i18n(I18n::global())
    }
}

// Helper trait for Diagnostic
trait DiagnosticHelpers {
    fn with_help_opt(self, help: Option<String>) -> Self;
}

impl DiagnosticHelpers for Diagnostic {
    fn with_help_opt(mut self, help: Option<String>) -> Self {
        if let Some(h) = help {
            self = self.with_help(h);
        }
        self
    }
}
```

**Update `src/driver/src/main.rs`**:
```rust
use simple_i18n::{I18n, Locale};
use clap::Parser as ClapParser;

#[derive(ClapParser)]
struct Cli {
    /// Input file
    file: String,

    /// Language for error messages (en, ko, ja)
    #[clap(long)]
    lang: Option<String>,
}

fn main() {
    let cli = Cli::parse();

    // Set up i18n
    let i18n = if let Some(lang) = &cli.lang {
        std::env::set_var("SIMPLE_LANG", lang);
        I18n::from_env()
    } else {
        I18n::from_env()
    };

    // Compile with i18n context
    match compile_file(&cli.file) {
        Ok(_) => println!("Compilation successful"),
        Err(errors) => {
            for error in errors {
                let diag = error.to_diagnostic_i18n(&i18n);
                eprintln!("{}", diag.format(&source, true));
            }
            std::process::exit(1);
        }
    }
}
```

### Phase 4: Testing & Validation

**Unit Tests**:
```rust
// In src/i18n/src/catalog.rs

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_load_default_locale() {
        let mut registry = CatalogRegistry::new()
            .with_catalog_dir("../../i18n");

        registry.load("en", "common").unwrap();

        let catalog = registry.get("en", "common").unwrap();
        let msg = catalog.get("error").unwrap();
        assert_eq!(msg.message, "error");
    }

    #[test]
    fn test_load_korean_locale() {
        let mut registry = CatalogRegistry::new()
            .with_catalog_dir("../../i18n");

        registry.load("ko", "common").unwrap();

        let catalog = registry.get("ko", "common").unwrap();
        let msg = catalog.get("error").unwrap();
        assert_eq!(msg.message, "오류");
    }

    #[test]
    fn test_fallback_chain() {
        let mut registry = CatalogRegistry::new()
            .with_catalog_dir("../../i18n");

        // Load both locales
        registry.load("en", "common").unwrap();
        registry.load("ko", "parser").unwrap();

        let locale = Locale::new("ko", None::<String>);

        // Korean message exists
        let msg = registry.get_message_with_fallback(&locale, "parser", "E0002");
        assert!(msg.unwrap().message.contains("예상"));

        // Message only in English - should fall back
        registry.load("en", "parser").unwrap();
        let msg = registry.get_message_with_fallback(&locale, "parser", "E0001");
        assert!(msg.is_some());  // Falls back to English
    }
}
```

**Integration Test**:
```rust
// In tests/i18n_integration.rs

use simple_i18n::I18n;
use simple_parser::Parser;

#[test]
fn test_korean_error_messages() {
    std::env::set_var("SIMPLE_LANG", "ko");

    let i18n = I18n::from_env();
    assert_eq!(i18n.locale().language_code(), "ko");

    // Parse invalid code
    let source = "fn main( return 0";  // Missing )
    let mut parser = Parser::new(source);
    let result = parser.parse();

    assert!(result.is_err());
    let error = result.unwrap_err();

    // Get Korean error message
    let diag = error.to_diagnostic_i18n(&i18n);
    let output = diag.format(source, false);

    assert!(output.contains("오류"));
    assert!(output.contains("E0010") || output.contains("E0002"));
}

#[test]
fn test_english_default() {
    std::env::remove_var("SIMPLE_LANG");

    let i18n = I18n::from_env();
    assert_eq!(i18n.locale().language_code(), "en");

    // Should use compiled-in defaults (zero I/O)
}
```

**Manual Testing Script** (`scripts/test_i18n.sh`):
```bash
#!/bin/bash

# Test Korean
echo "=== Testing Korean ==="
cat > /tmp/test_ko.spl << 'EOF'
fn main(
    return 0
EOF

./target/debug/simple build /tmp/test_ko.spl --lang ko
# Expected: 오류[E0010]: 필요한 토큰이 누락되었습니다

# Test English
echo "=== Testing English ==="
./target/debug/simple build /tmp/test_ko.spl --lang en
# Expected: error[E0010]: missing expected token

# Test environment variable
echo "=== Testing SIMPLE_LANG env ==="
SIMPLE_LANG=ko ./target/debug/simple build /tmp/test_ko.spl
# Expected: 오류[E0010]: ...

echo "=== All tests complete ==="
```

---

## Refactoring Strategy

### Step 1: Minimal Viable Product (MVP)

**Goal**: Get Korean errors working end-to-end

**Scope**:
- ✅ Locale suffix support (`__init__.ko.spl`)
- ✅ Runtime loading
- ✅ Fallback to English
- ✅ CLI `--lang` flag
- ❌ No compile-time embedding yet (Phase 2)

**Timeline**: 1-2 days

### Step 2: Performance Optimization

**Goal**: Zero-cost default locale

**Scope**:
- ✅ Build-time catalog compilation
- ✅ phf perfect hash maps
- ✅ Embedded defaults

**Timeline**: 2-3 days

### Step 3: Full Coverage

**Goal**: All error types localized

**Scope**:
- ✅ Parser errors (E0001-E0012)
- ✅ Compiler errors (E1xxx-E3xxx)
- ✅ Lint messages
- ✅ Verification errors

**Timeline**: 3-5 days

### Step 4: Polish

**Goal**: Production ready

**Scope**:
- ✅ Documentation complete
- ✅ Tests passing
- ✅ Performance benchmarks
- ✅ Translation guide

**Timeline**: 1-2 days

---

## Success Criteria

### Functional Requirements

- [ ] Load `i18n/__init__.ko.spl` successfully
- [ ] CLI flag `--lang ko` works end-to-end
- [ ] Environment variable `SIMPLE_LANG=ko` works
- [ ] Fallback to English for missing translations
- [ ] Parser errors display in Korean
- [ ] Severity names localized ("error" → "오류")

### Performance Requirements

- [ ] Default locale: 0ns overhead (compile-time)
- [ ] Korean locale: < 5ms first load
- [ ] Binary size increase: < 20KB with embedded English
- [ ] Memory usage: < 100KB per locale

### Quality Requirements

- [ ] All unit tests passing
- [ ] Integration tests passing
- [ ] Documentation complete
- [ ] Korean translations reviewed by native speaker

---

## Migration Checklist

### Phase 1: Foundation
- [ ] Update `src/i18n/src/catalog.rs` for locale suffix
- [ ] Add fallback logic to `CatalogRegistry`
- [ ] Update `SimpleCatalogParser` if needed
- [ ] Write unit tests for locale loading
- [ ] Test: `cargo test -p simple_i18n`

### Phase 2: Build System
- [ ] Add `phf` dependencies
- [ ] Create `src/i18n/build.rs`
- [ ] Implement catalog parser in build script
- [ ] Generate default catalogs at build time
- [ ] Test: `cargo build -p simple_i18n`

### Phase 3: Integration
- [ ] Add `simple_i18n` to parser/compiler dependencies
- [ ] Update `ParseError::to_diagnostic_i18n()`
- [ ] Add `--lang` flag to CLI
- [ ] Update driver to use i18n
- [ ] Test: Manual testing with test files

### Phase 4: Documentation
- [ ] Create `doc/guide/i18n.md`
- [ ] Create `doc/contributing/i18n_translation.md`
- [ ] Create `doc/spec/i18n_architecture.md`
- [ ] Update `CLAUDE.md`
- [ ] Update `README.md`
- [ ] Update `doc/architecture/overview.md`

### Phase 5: Validation
- [ ] Run integration tests
- [ ] Manual testing with Korean locale
- [ ] Performance benchmarks
- [ ] Code review
- [ ] Native speaker review (Korean)

---

## File Checklist

### New Files to Create
- [ ] `src/i18n/build.rs` - Build script
- [ ] `src/i18n/src/codegen/mod.rs` - Codegen utilities
- [ ] `doc/guide/i18n.md` - User guide
- [ ] `doc/contributing/i18n_translation.md` - Contributor guide
- [ ] `doc/spec/i18n_architecture.md` - Technical spec
- [ ] `tests/i18n_integration.rs` - Integration tests
- [ ] `scripts/test_i18n.sh` - Manual test script

### Files to Modify
- [ ] `src/i18n/Cargo.toml` - Add phf dependencies
- [ ] `src/i18n/src/catalog.rs` - Locale suffix support
- [ ] `src/i18n/src/lib.rs` - Include generated code
- [ ] `src/parser/src/error.rs` - Add `to_diagnostic_i18n()`
- [ ] `src/driver/src/main.rs` - Add `--lang` flag
- [ ] `CLAUDE.md` - Add i18n section
- [ ] `README.md` - Mention i18n feature
- [ ] `doc/architecture/overview.md` - Add i18n subsystem

### Files Already Exist (No Changes)
- ✅ `i18n/__init__.spl`
- ✅ `i18n/__init__.ko.spl`
- ✅ `i18n/parser.spl`
- ✅ `i18n/parser.ko.spl`

---

## Summary

This plan provides a complete roadmap to integrate Rust compiler with Simple language `__init__` i18n files. The implementation is divided into clear phases with defined success criteria, allowing for incremental progress and early validation.

**Key Innovations**:
1. **Locale suffix pattern** (`__init__.ko.spl`) - clear and extensible
2. **Build-time embedding** - zero-cost default locale
3. **Automatic fallback** - robust error handling
4. **Simple language for data** - dogfooding approach

**Next Steps**: Start with Phase 1 (Foundation) to get basic locale loading working.
