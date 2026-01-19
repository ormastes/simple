# I18n Message Catalogs

This directory contains internationalized error messages for the Simple compiler.

## File Structure

```
i18n/
├── __init__.spl       # English common UI (severity names) - DEFAULT
├── __init__.ko.spl    # Korean common UI
├── parser.spl         # English parser errors (E0001-E0012) - DEFAULT
├── parser.ko.spl      # Korean parser errors
├── compiler.spl       # English compiler errors (future)
└── compiler.ko.spl    # Korean compiler errors (future)
```

## Naming Convention

**Pattern**: `<basename>.<locale>.spl`

- **Default (English)**: No suffix (e.g., `__init__.spl`, `parser.spl`)
- **Korean**: `.ko` suffix (e.g., `__init__.ko.spl`, `parser.ko.spl`)
- **Japanese**: `.ja` suffix (e.g., `__init__.ja.spl`, `parser.ja.spl`)

## File Contents

### Common UI (`__init__.spl`)

Contains UI strings like severity names:

```simple
val severity = {
    "error": "error",
    "warning": "warning",
    "info": "info",
    "help": "help",
    "note": "note"
}
```

### Parser Errors (`parser.spl`)

Contains error message templates:

```simple
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
    }

    // ... E0003-E0012
}
```

## Usage

### From Command Line

```bash
# Default (English)
simple build main.spl

# Korean
simple build main.spl --lang ko

# Environment variable
export SIMPLE_LANG=ko
simple build main.spl
```

### From Rust Code

```rust
use simple_i18n::{I18n, MessageContext};

// Auto-detect locale from environment
let i18n = I18n::from_env();

// Get severity name
let error_text = i18n.get_severity("error");
// Returns: "오류" (if SIMPLE_LANG=ko) or "error" (default)

// Get error message with interpolation
let mut ctx = MessageContext::new();
ctx.insert("expected", "identifier");
ctx.insert("found", "number");

let msg = i18n.get_message("parser", "E0002", &ctx);
// Returns localized message with placeholders filled in
```

## Adding Translations

1. **Create locale file**:
   ```bash
   cp __init__.spl __init__.ja.spl
   cp parser.spl parser.ja.spl
   ```

2. **Translate content**:
   ```simple
   # __init__.ja.spl
   val severity = {
       "error": "エラー",
       "warning": "警告",
       ...
   }
   ```

3. **Test**:
   ```bash
   simple build test.spl --lang ja
   ```

4. **Submit PR** with translation files

## Translation Guidelines

- ✅ Keep `{placeholder}` syntax unchanged
- ✅ Maintain error code structure (`"E0001"`, etc.)
- ✅ Use professional/formal tone
- ✅ Get native speaker review before merging
- ❌ Don't translate placeholder names (`{expected}`, `{found}`)
- ❌ Don't modify error codes or IDs

## How It Works

1. **Build time**: Default English catalog compiled into binary (zero-cost)
2. **Runtime**: Requested locale loaded from `.ko.spl` files on-demand
3. **Fallback**: Missing translations fall back to English automatically

## Documentation

- **Complete spec**: `doc/design/i18n_complete_specification.md`
- **Implementation plan**: `doc/design/i18n_rust_integration_plan.md`
- **User guide**: `doc/guide/i18n.md` (coming soon)
- **Contributor guide**: `doc/contributing/i18n_translation.md` (coming soon)

## Supported Languages

| Language | Code | Status | Files |
|----------|------|--------|-------|
| English | en | ✅ Complete | `__init__.spl`, `parser.spl` |
| Korean | ko | ✅ Complete | `__init__.ko.spl`, `parser.ko.spl` |
| Japanese | ja | 📋 Planned | - |
| Chinese | zh | 📋 Planned | - |

## Implementation Status

- ✅ File structure created
- ✅ English and Korean content written
- 🚧 Rust integration in progress
- 📋 CLI `--lang` flag planned
- 📋 Build-time compilation planned

## Questions?

See `doc/design/i18n_complete_specification.md` for full details, or ask in the Simple language community.
