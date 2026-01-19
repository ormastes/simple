# Simple Language I18n Complete Specification

## Executive Summary

This document provides the complete specification for Simple's internationalization (i18n) system, explaining how Rust compiler works with Simple language `__init__` files for multi-language error messages.

**Status**: Design Complete, Implementation In Progress

---

## System Overview

### What It Does

Allows Simple compiler to display error messages in multiple languages:
- **English** (default) - Compiled into binary, zero runtime cost
- **Korean** - Loaded at runtime from `.ko.spl` files
- **Japanese, Chinese, etc.** - Easy to add

### How It Works

```
User writes:          fn main( return 0     ← Missing )
                              ↓
Compiler parses  →    ParseError::MissingToken { expected: ")", ... }
                              ↓
I18n system      →    Load i18n/__init__.ko.spl
                              ↓
Display:              오류[E0010]: 필요한 토큰이 누락되었습니다: )
                                   여기에 )이(가) 필요합니다
```

---

## File Structure

### Directory Layout

```
simple/
├── i18n/                      # I18n catalog directory (workspace root)
│   ├── __init__.spl           # English common UI (default)
│   ├── __init__.ko.spl        # Korean common UI
│   ├── parser.spl             # English parser errors
│   ├── parser.ko.spl          # Korean parser errors
│   ├── compiler.spl           # English compiler errors (future)
│   └── compiler.ko.spl        # Korean compiler errors (future)
│
└── src/
    └── i18n/                  # Rust i18n implementation
        ├── Cargo.toml
        ├── build.rs           # Compile-time catalog generator
        └── src/
            ├── lib.rs         # Public API
            ├── locale.rs      # Locale detection
            ├── catalog.rs     # Catalog loading
            ├── message.rs     # Message interpolation
            ├── simple_catalog.rs  # Simple parser integration
            └── bootstrap.rs   # Fallback messages
```

### File Naming Convention

**Pattern**: `<basename>.<locale>.spl`

| File Type | Default (English) | Korean | Japanese |
|-----------|-------------------|--------|----------|
| Common UI | `__init__.spl` | `__init__.ko.spl` | `__init__.ja.spl` |
| Parser errors | `parser.spl` | `parser.ko.spl` | `parser.ja.spl` |
| Compiler errors | `compiler.spl` | `compiler.ko.spl` | `compiler.ja.spl` |

**Rules**:
- Default locale: **no suffix**
- Other locales: **locale code suffix** before `.spl`
- Locale codes: ISO 639-1 (2-letter): `ko`, `ja`, `zh`, `fr`, `de`

---

## File Format

### Content Structure

I18n files use **Simple language** (not JSON), but with relaxed rules since they're data files:

```simple
# i18n/__init__.spl - English common UI

# Dictionary with severity names
val severity = {
    "error": "error",
    "warning": "warning",
    "info": "info",
    "help": "help",
    "note": "note"
}

# Optional: Formatting functions
fn format_error_count(n: Int) -> String:
    if n == 1:
        "1 error"
    else:
        "{n} errors"
```

```simple
# i18n/__init__.ko.spl - Korean overlay

val severity = {
    "error": "오류",
    "warning": "경고",
    "info": "정보",
    "help": "도움말",
    "note": "참고"
}

fn format_error_count(n: Int) -> String:
    if n == 1:
        "오류 1개"
    else:
        "오류 {n}개"
```

### Parser Errors

```simple
# i18n/parser.spl

val messages = {
    "E0001": {
        "id": "E0001",
        "title": "Syntax Error",
        "message": "{message}",
        "label": "syntax error here"
    },

    "E0002": {
        "id": "E0002",
        "title": "Unexpected Token",
        "message": "unexpected token: expected {expected}, found {found}",
        "label": "expected {expected} here",
        "help": "try adding `{expected}` before this token"
    },

    // ... E0003-E0012
}
```

### What's Allowed vs Forbidden

**✅ ALLOWED in i18n files**:
- Variables (`val severity = {...}`)
- Functions (`fn format_error_count(...)`)
- Constants
- Comments

**❌ FORBIDDEN in i18n files**:
- Module declarations (`mod common`)
- Imports (`use`, `export use`, `common use`)
- Child modules (`pub mod something`)
- Types/structs/classes

**Rationale**: I18n files are **data files** parsed by Rust, not Simple modules. They don't participate in the module system.

---

## Architecture

### Three Layers

```
┌──────────────────────────────────────────────────┐
│ Layer 1: Build-Time Compilation                 │
│                                                  │
│ At cargo build:                                  │
│  1. Parse i18n/__init__.spl                     │
│  2. Extract val severity = {...}                │
│  3. Generate Rust code:                         │
│     pub const DEFAULT_SEVERITY: phf::Map = ...  │
│  4. Embed in binary (~10KB)                     │
│                                                  │
│ Result: Zero-cost default locale access         │
└──────────────────────────────────────────────────┘
                        ↓
┌──────────────────────────────────────────────────┐
│ Layer 2: Runtime Loading                        │
│                                                  │
│ When user runs: simple build --lang ko          │
│  1. Detect locale from CLI/env                  │
│  2. Check if locale == default → No             │
│  3. Load i18n/__init__.ko.spl from disk         │
│  4. Parse Simple code (~1-2ms)                  │
│  5. Cache in memory (HashMap)                   │
│                                                  │
│ Result: Runtime catalog available               │
└──────────────────────────────────────────────────┘
                        ↓
┌──────────────────────────────────────────────────┐
│ Layer 3: Message Retrieval                      │
│                                                  │
│ When compiler needs error message:              │
│  1. i18n.get_message("parser", "E0002", ctx)   │
│  2. Try requested locale (ko)                   │
│     → Found: Return Korean message              │
│     → Not found: Fall back to default (en)      │
│  3. Interpolate {placeholders}                  │
│  4. Return to compiler                          │
│                                                  │
│ Result: Localized error message                 │
└──────────────────────────────────────────────────┘
```

### Locale Resolution Algorithm

```
Input: locale="ko_KR", domain="parser", id="E0002"

Step 1: Try full locale
  ├─ Check: i18n/parser.ko_KR.spl exists?
  └─ No → Continue to Step 2

Step 2: Try language only
  ├─ Check: i18n/parser.ko.spl exists?
  ├─ Yes → Parse file
  ├─ Check: Does "E0002" exist in catalog?
  └─ Yes → Return Korean message ✓

Step 3: Fall back to default
  ├─ Check: DEFAULT_PARSER_MESSAGES["E0002"]
  └─ Return English message ✓

Result: Always returns a message (never fails)
```

---

## API Reference

### Rust API

```rust
use simple_i18n::{I18n, MessageContext, Locale};

// Create I18n instance
let i18n = I18n::from_env();           // Auto-detect from SIMPLE_LANG
let i18n = I18n::with_locale("ko");    // Explicit locale
let i18n = I18n::default();            // Use default (English)

// Get severity name
let error_text = i18n.get_severity("error");
// Returns: "오류" (if locale=ko) or "error" (if locale=en)

// Get error message with interpolation
let mut ctx = MessageContext::new();
ctx.insert("expected", "identifier");
ctx.insert("found", "number");

let msg = i18n.get_message("parser", "E0002", &ctx);
// Returns: InterpolatedMessage {
//   id: "E0002",
//   title: "예상치 못한 토큰",
//   message: "identifier을(를) 예상했지만 number을(를) 발견했습니다",
//   label: Some("여기에 identifier이(가) 필요합니다"),
//   ...
// }
```

### CLI Interface

```bash
# Use default locale (from LANG environment variable or English)
simple build main.spl

# Explicit Korean
simple build main.spl --lang ko

# Environment variable
export SIMPLE_LANG=ko
simple build main.spl

# Japanese
simple build main.spl --lang ja
```

### Output Examples

**English** (default):
```
error[E0002]: unexpected token: expected identifier, found number
  --> main.spl:5:10
   |
 5 |     val x = 123abc
   |             ^^^^^^ expected identifier here
   |
   = help: try adding `identifier` before this token
```

**Korean** (`--lang ko`):
```
오류[E0002]: identifier을(를) 예상했지만 number을(를) 발견했습니다
  --> main.spl:5:10
   |
 5 |     val x = 123abc
   |             ^^^^^^ 여기에 identifier이(가) 필요합니다
   |
   = 도움말: 이 토큰 앞에 `identifier`를 추가해 보세요
```

---

## Performance Characteristics

### Default Locale (English)

```rust
// Compile-time embedded
pub const DEFAULT_SEVERITY: phf::Map<&str, &str> = phf_map! {
    "error" => "error",
    "warning" => "warning",
    ...
};

// Runtime access - ZERO cost
let error_text = DEFAULT_SEVERITY.get("error");
// Equivalent to: "error" (compile-time constant)
```

**Metrics**:
- Access time: **0ns** (compile-time constant)
- I/O operations: **0** (no disk access)
- Parsing: **0ms** (pre-parsed at build time)
- Binary size: **~10KB** (English catalogs embedded)

### Runtime Locale (Korean)

```rust
// First access - parse from disk
let i18n = I18n::with_locale("ko");
// Parses i18n/__init__.ko.spl (~1-2ms)

// Subsequent access - cached
let error_text = i18n.get_severity("error");
// HashMap lookup (~1ns)
```

**Metrics**:
- First access: **1-2ms** (parse + cache)
- Subsequent access: **~1ns** (HashMap lookup)
- I/O operations: **1** (load .ko.spl file)
- Memory: **~100KB** (Korean catalog in memory)

---

## Implementation Status

### ✅ Completed

- [x] File structure created (`i18n/__init__.spl`, `i18n/__init__.ko.spl`)
- [x] Basic i18n crate structure (`src/i18n/`)
- [x] Locale detection (`Locale::from_env()`)
- [x] Message interpolation (`MessageContext`)
- [x] Bootstrap fallback messages
- [x] Design documentation

### 🚧 In Progress

- [ ] Locale suffix support in `CatalogRegistry`
- [ ] Fallback chain implementation
- [ ] Build-time catalog compilation (`build.rs`)
- [ ] Parser integration (`ParseError::to_diagnostic_i18n()`)
- [ ] CLI `--lang` flag

### 📋 Planned

- [ ] Compiler error localization
- [ ] Lint message localization
- [ ] Japanese translation
- [ ] Chinese translation
- [ ] Performance benchmarks
- [ ] Native speaker review

---

## Adding New Translations

### Step-by-Step Guide

**1. Create locale files**
```bash
cd i18n
cp __init__.spl __init__.ja.spl
cp parser.spl parser.ja.spl
```

**2. Translate content**
```simple
# i18n/__init__.ja.spl

val severity = {
    "error": "エラー",
    "warning": "警告",
    "info": "情報",
    "help": "ヘルプ",
    "note": "注"
}
```

**3. Test**
```bash
simple build test.spl --lang ja
```

**4. Submit PR**
Include:
- New `.ja.spl` files
- Test results
- Native speaker review

### Translation Guidelines

- **Keep {placeholders}** - Don't translate `{expected}`, `{found}`, etc.
- **Match structure** - Keep same error codes and field names
- **Use formal tone** - Professional language for compiler messages
- **Test thoroughly** - Verify with actual error cases
- **Get review** - Native speaker should review before merging

---

## Troubleshooting

### Issue: Korean characters not displaying

**Cause**: Terminal encoding not set to UTF-8

**Solution**:
```bash
export LANG=ko_KR.UTF-8
export LC_ALL=ko_KR.UTF-8
```

### Issue: Locale file not found

**Error**: `CatalogLoadError: i18n/__init__.ko.spl`

**Cause**: Locale file doesn't exist or wrong path

**Solution**:
1. Check file exists: `ls i18n/__init__.ko.spl`
2. Check working directory: `pwd` (should be workspace root)
3. Verify file path in error message

### Issue: Falling back to English unexpectedly

**Symptom**: Korean locale set, but getting English messages

**Debug**:
```rust
// Check which locale is active
println!("Locale: {}", i18n.locale().language_code());

// Check if catalog loaded
println!("Catalogs: {:?}", registry.catalogs.keys());
```

**Common causes**:
1. Locale file has parse errors
2. Message ID missing in Korean catalog
3. Working as designed (fallback for missing keys)

---

## Future Enhancements

### v1.1 (Short-term)

- [ ] Additional languages (Japanese, Chinese, Spanish, French)
- [ ] Improved Korean particle selection (조사 처리)
- [ ] Translation coverage metrics
- [ ] LSP integration (hover messages in user's language)

### v2.0 (Medium-term)

- [ ] CLDR plural rules for all languages
- [ ] Locale-aware number formatting
- [ ] Date/time formatting
- [ ] Community translation platform
- [ ] Translation validation tool

### v3.0 (Long-term)

- [ ] AI-assisted translation suggestions
- [ ] Translation memory system
- [ ] Crowdsourced translations
- [ ] Real-time translation updates

---

## References

### Related Documents

- `doc/design/i18n_simple_lang_plan.md` - Original plan (JSON-based, superseded)
- `doc/design/i18n_init_locale_spec.md` - Locale-aware __init__ specification
- `doc/design/i18n_rust_integration_plan.md` - Implementation roadmap
- `doc/guide/module_system.md` - Simple module system (for context)

### External References

- ISO 639-1: Language codes - https://en.wikipedia.org/wiki/ISO_639-1
- BCP 47: Language tags - https://tools.ietf.org/html/bcp47
- Rust i18n crates: fluent-rs, gettext-rs, rosetta-rs
- Compiler i18n: GCC (gettext), Rust (Fluent), Swift (strings files)

---

## Summary

The Simple language i18n system uses Simple's own language for message catalogs, providing:

1. **Self-hosting** - Compiler uses Simple for configuration
2. **Performance** - Zero-cost default locale via compile-time embedding
3. **Extensibility** - Easy to add new languages with `.ko.spl` pattern
4. **Robustness** - Automatic fallback ensures messages always display

**File pattern**: `__init__.spl` (default), `__init__.ko.spl` (Korean)

**Rust integration**: Parse Simple files, embed defaults at build-time, load locales at runtime

**User experience**: `simple build --lang ko` → Korean error messages

This design balances performance, developer experience, and maintainability while showcasing Simple's capabilities.
