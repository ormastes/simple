# I18n Implementation Plan: Simple Language Catalogs

## Overview

Instead of using JSON files for i18n message catalogs, we'll use **Simple language itself** to define error messages. This "dogfooding" approach allows:

1. **Self-hosting**: The compiler uses its own language for configuration
2. **Type safety**: Simple's type system validates message structure
3. **Developer experience**: Contributors write Simple code, not JSON
4. **Testing**: i18n files serve as real-world Simple code examples

## Architecture

### Catalog File Structure

```
src/i18n/locales/
├── en/
│   ├── __init__.spl          # Common UI strings (severity names, etc.)
│   ├── parser.spl            # Parser error messages (E0001-E0012)
│   ├── compiler.spl          # Compiler error messages (E1xxx-E3xxx)
│   └── lint.spl              # Lint messages
└── ko/
    ├── __init__.spl          # Korean UI strings
    ├── parser.spl            # Korean parser errors
    ├── compiler.spl          # Korean compiler errors
    └── lint.spl              # Korean lint messages
```

### Simple Language Catalog Format

Each catalog file exports a dictionary/map of message IDs to message structures:

```simple
# src/i18n/locales/en/parser.spl

# Message catalog for parser errors
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

    "E0003": {
        "id": "E0003",
        "title": "Unexpected End of File",
        "message": "unexpected end of file",
        "note": "the file ended unexpectedly",
        "help": "check for unclosed brackets or missing statements"
    }
}
```

Korean version:

```simple
# src/i18n/locales/ko/parser.spl

val messages = {
    "E0001": {
        "id": "E0001",
        "title": "구문 오류",
        "message": "{message}",
        "label": "여기에 구문 오류가 있습니다"
    },

    "E0002": {
        "id": "E0002",
        "title": "예상치 못한 토큰",
        "message": "{expected}을(를) 예상했지만 {found}을(를) 발견했습니다",
        "label": "여기에 {expected}이(가) 필요합니다",
        "help": "이 토큰 앞에 `{expected}`를 추가해 보세요"
    }
}
```

Common UI strings:

```simple
# src/i18n/locales/en/__init__.spl

val severity = {
    "error": "error",
    "warning": "warning",
    "info": "info",
    "help": "help",
    "note": "note"
}
```

```simple
# src/i18n/locales/ko/__init__.spl

val severity = {
    "error": "오류",
    "warning": "경고",
    "info": "정보",
    "help": "도움말",
    "note": "참고"
}
```

## Implementation Phases

### Phase 1: Simple Catalog Parser (Rust)

**Create:** `src/src/i18n/src/simple_catalog.rs`

This module parses Simple language catalog files and extracts message data:

```rust
pub struct SimpleCatalogParser {
    parser: SimpleParser,
}

impl SimpleCatalogParser {
    /// Parse a Simple catalog file and extract messages
    pub fn parse_catalog(path: &Path) -> Result<MessageCatalog> {
        // 1. Read and parse the Simple file
        // 2. Look for `val messages = { ... }` declaration
        // 3. Extract dictionary literals as messages
        // 4. Build MessageCatalog struct
    }

    /// Extract a message from a dictionary AST node
    fn extract_message(dict: &DictLiteral) -> Result<LocalizedMessage> {
        // Parse fields: id, title, message, label, help, note
    }
}
```

**Key considerations:**
- **Bootstrap problem**: Parser errors can't use i18n if parser hasn't loaded yet
- **Solution**: Hardcode minimal English fallback messages in Rust for bootstrap errors
- Use the Simple parser to parse catalog files
- Extract AST nodes (dict literals, string literals) into message structs

### Phase 2: Update I18n System

**Modify:** `src/src/i18n/src/catalog.rs`

Remove JSON loading, add Simple catalog loading:

```rust
impl MessageCatalog {
    /// Load a message catalog from a Simple language file
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self> {
        SimpleCatalogParser::parse_catalog(path.as_ref())
    }
}

impl CatalogRegistry {
    /// Load a catalog from the catalog directory
    ///
    /// Expects files in the format: `{catalog_dir}/{locale}/{domain}.spl`
    pub fn load(&mut self, locale: &str, domain: &str) -> Result<()> {
        let catalog_dir = self.catalog_dir.as_ref()
            .ok_or_else(|| I18nError::CatalogDirectoryNotFound("not set".to_string()))?;

        let path = catalog_dir.join(locale).join(format!("{}.spl", domain));

        // Special case: __init__.spl for common strings
        let path = if domain == "common" {
            catalog_dir.join(locale).join("__init__.spl")
        } else {
            catalog_dir.join(locale).join(format!("{}.spl", domain))
        };

        let catalog = MessageCatalog::load(&path)?;
        self.register(catalog);
        Ok(())
    }
}
```

### Phase 3: Bootstrap Fallback

**Create:** `src/src/i18n/src/bootstrap.rs`

Hardcode minimal English messages for bootstrap errors:

```rust
/// Bootstrap messages used when catalogs can't be loaded
pub const BOOTSTRAP_MESSAGES: &[(&str, &str)] = &[
    ("E0001", "Syntax error"),
    ("E0002", "Unexpected token"),
    ("E0003", "Unexpected end of file"),
    // ... minimal set of parser errors
];

impl I18n {
    /// Get a message with bootstrap fallback
    pub fn get_message_safe(&self, domain: &str, id: &str, ctx: &MessageContext)
        -> InterpolatedMessage
    {
        // Try catalog first
        if let Some(msg) = self.get_message(domain, id, ctx) {
            return msg;
        }

        // Fall back to bootstrap
        if let Some(msg) = BOOTSTRAP_MESSAGES.iter().find(|(code, _)| *code == id) {
            return InterpolatedMessage {
                id: id.to_string(),
                title: msg.1.to_string(),
                message: msg.1.to_string(),
                label: None,
                help: None,
                note: None,
            };
        }

        // Last resort
        InterpolatedMessage {
            id: id.to_string(),
            title: "Error".to_string(),
            message: format!("Error {}", id),
            label: None,
            help: None,
            note: None,
        }
    }
}
```

### Phase 4: Write Catalogs in Simple

**Create catalog files:**
1. `src/i18n/locales/en/__init__.spl` - English UI strings
2. `src/i18n/locales/en/parser.spl` - English parser errors (E0001-E0012)
3. `src/i18n/locales/ko/__init__.spl` - Korean UI strings
4. `src/i18n/locales/ko/parser.spl` - Korean parser errors

### Phase 5: Integration

Same as before:
- Add `--lang` CLI flag
- Update `ParseError::to_diagnostic()` to use i18n
- Add tests

## Benefits of Simple Language Catalogs

### 1. Self-Hosting
The compiler uses its own language, demonstrating confidence in Simple's capabilities.

### 2. Type Safety
Simple's type system can validate message structure:
```simple
# Future: Define Message type
struct Message:
    id: String
    title: String
    message: String
    label: String?
    help: String?
    note: String?

val messages: Map<String, Message> = { ... }
```

### 3. Better DX for Contributors
Contributors familiar with Simple can add translations without learning JSON schema.

### 4. Living Documentation
Catalog files serve as examples of Simple syntax (dict literals, string literals, etc.).

### 5. Compiler Testing
Parsing catalog files tests the parser with real-world Simple code.

## Challenges and Solutions

### Challenge 1: Bootstrap Problem
**Problem**: Can't parse Simple files to get error messages if parser fails.

**Solution**:
- Hardcode minimal English fallback messages in Rust
- Use fallbacks only for parser bootstrap errors
- Once parser is working, load full catalogs

### Challenge 2: Performance
**Problem**: Parsing Simple files might be slower than loading JSON.

**Solution**:
- Parse catalogs once at startup, cache in memory
- Pre-compile catalogs to binary format for release builds (future optimization)
- Lazy-load catalogs only when needed

### Challenge 3: Syntax Dependencies
**Problem**: Catalog files depend on Simple syntax (dict literals, etc.) being supported.

**Solution**:
- Start with simple syntax (string literals, dict literals)
- These are basic features already implemented in Simple parser
- Can extend to more complex structures later

### Challenge 4: Circular Dependency
**Problem**: Parser needs catalogs, catalogs need parser.

**Solution**:
- Use a two-stage approach:
  1. Bootstrap: Use hardcoded Rust messages
  2. Full mode: Load Simple catalogs after parser is initialized
- Parser errors during catalog loading use bootstrap messages

## Implementation Timeline

### Phase 1: Foundation (Days 1-2)
- Design Simple catalog format (dict literal structure)
- Implement SimpleCatalogParser in Rust
- Add bootstrap fallback system

### Phase 2: Catalogs (Days 3-4)
- Write English catalogs (__init__.spl, parser.spl)
- Write Korean catalogs
- Test catalog loading

### Phase 3: Integration (Days 5-6)
- Update I18n system to use Simple catalogs
- Integrate with Diagnostic
- Add --lang CLI flag
- Migrate ParseError to use i18n

### Phase 4: Testing & Polish (Day 7)
- Unit tests for catalog parser
- Integration tests for Korean errors
- Documentation
- Native speaker review

## Example Usage

After implementation, the workflow is:

```bash
# Default (English)
simple build main.spl
# error[E0002]: unexpected token: expected identifier, found number

# Korean
simple build main.spl --lang ko
# 오류[E0002]: 식별자을(를) 예상했지만 숫자을(를) 발견했습니다

# Environment variable
export SIMPLE_LANG=ko
simple build main.spl
# 오류[E0002]: 식별자을(를) 예상했지만 숫자을(를) 발견했습니다
```

## Success Criteria

✅ MVP Complete When:
1. SimpleCatalogParser can parse Simple catalog files
2. Bootstrap fallback works for parser errors
3. English and Korean catalogs written in Simple
4. `--lang ko` flag produces Korean error messages
5. All tests passing

## Future Enhancements

### v1.1
- Type-safe Message struct in Simple
- Validation of message structure at catalog parse time
- More languages (Japanese, Chinese, Spanish)

### v2.0
- Pre-compiled binary catalog format for faster loading
- LSP integration for translated hover messages
- Catalog validation tool (check for missing translations)

### v3.0
- Community-contributed translations
- Translation coverage metrics
- Automatic translation suggestions using LLMs
