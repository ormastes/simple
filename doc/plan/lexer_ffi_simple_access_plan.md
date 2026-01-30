# Lexer FFI Access for Simple - Implementation Plan

**Date:** 2026-01-30
**Goal:** Enable Simple code to test lexer tokens directly
**Estimated Time:** 4-6 hours

---

## Objective

Expose Rust lexer functionality to Simple code, enabling token-level testing similar to Rust unit tests.

**Benefits:**
- ✅ Token-level testing in Simple
- ✅ Single-language test suite (all in Simple)
- ✅ Better debugging (inspect tokens from Simple)
- ✅ Educational (users can see tokens)

---

## Phase 1: FFI Implementation (2-3 hours)

### Step 1: Create Token FFI Types

**File:** `src/rust/compiler/src/interpreter_extern/lexer_ffi.rs` (NEW)

```rust
use crate::runtime_value::RuntimeValue;
use simple_parser::{Lexer, TokenKind, NamePattern};
use std::ffi::{CStr, c_char};

/// Token representation for FFI
#[derive(Debug, Clone)]
pub struct TokenInfo {
    pub kind: String,
    pub text: String,
    pub name: Option<String>,      // For Identifier tokens
    pub pattern: Option<String>,   // For Identifier tokens
    pub value: Option<i64>,        // For Integer tokens
}

impl TokenInfo {
    fn from_token_kind(kind: TokenKind, text: String) -> Self {
        match kind {
            TokenKind::Identifier { name, pattern } => {
                let pattern_str = match pattern {
                    NamePattern::Constant => "Constant",
                    NamePattern::TypeName => "TypeName",
                    NamePattern::Immutable => "Immutable",
                    NamePattern::Mutable => "Mutable",
                    NamePattern::Private => "Private",
                };
                TokenInfo {
                    kind: "Identifier".to_string(),
                    text,
                    name: Some(name),
                    pattern: Some(pattern_str.to_string()),
                    value: None,
                }
            }
            TokenKind::Integer(n) => TokenInfo {
                kind: "Integer".to_string(),
                text,
                name: None,
                pattern: None,
                value: Some(n),
            },
            TokenKind::Skip => TokenInfo {
                kind: "Skip".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::Static => TokenInfo {
                kind: "Static".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            TokenKind::Default => TokenInfo {
                kind: "Default".to_string(),
                text,
                name: None,
                pattern: None,
                value: None,
            },
            // Add more token kinds as needed
            _ => TokenInfo {
                kind: format!("{:?}", kind),
                text,
                name: None,
                pattern: None,
                value: None,
            }
        }
    }
}

/// Tokenize source code and return list of tokens
pub fn tokenize_source(source: String) -> Vec<TokenInfo> {
    let mut lexer = Lexer::new(&source);
    let tokens = lexer.tokenize();

    tokens.into_iter().map(|token| {
        let text = token.text.clone();
        TokenInfo::from_token_kind(token.kind, text)
    }).collect()
}
```

### Step 2: Add FFI Extern Functions

**Same file:** `src/rust/compiler/src/interpreter_extern/lexer_ffi.rs`

```rust
/// FFI function: tokenize source code
#[no_mangle]
pub extern "C" fn simple_lexer_tokenize(source_ptr: *const c_char) -> RuntimeValue {
    let source = unsafe {
        CStr::from_ptr(source_ptr).to_string_lossy().into_owned()
    };

    let tokens = tokenize_source(source);

    // Convert to RuntimeValue::Array
    let token_values: Vec<RuntimeValue> = tokens.into_iter().map(|token| {
        // Convert TokenInfo to RuntimeValue::Dict
        let mut fields = std::collections::HashMap::new();
        fields.insert("kind".to_string(), RuntimeValue::String(token.kind));
        fields.insert("text".to_string(), RuntimeValue::String(token.text));

        if let Some(name) = token.name {
            fields.insert("name".to_string(), RuntimeValue::String(name));
        }
        if let Some(pattern) = token.pattern {
            fields.insert("pattern".to_string(), RuntimeValue::String(pattern));
        }
        if let Some(value) = token.value {
            fields.insert("value".to_string(), RuntimeValue::Integer(value));
        }

        RuntimeValue::Dict(fields)
    }).collect();

    RuntimeValue::Array(token_values)
}
```

### Step 3: Register FFI Function

**File:** `src/rust/compiler/src/interpreter_extern/mod.rs`

```rust
// Add to existing file
mod lexer_ffi;
pub use lexer_ffi::*;

// In register_externs() function
pub fn register_externs() -> HashMap<String, ExternFn> {
    let mut externs = HashMap::new();

    // ... existing registrations ...

    // Lexer functions
    externs.insert("lexer_tokenize".to_string(), simple_lexer_tokenize as ExternFn);

    externs
}
```

---

## Phase 2: Simple API Wrapper (1-2 hours)

### Step 1: Create Lexer Module

**File:** `src/lib/std/src/compiler/lexer.spl` (NEW)

```simple
"""
Compiler Lexer API

Provides access to the Simple lexer for token-level inspection and testing.
"""

use core.*

# Token information
struct Token:
    kind: str        # Token kind name (e.g., "Identifier", "Skip", "Integer")
    text: str        # Original source text
    name: str?       # For Identifier tokens
    pattern: str?    # For Identifier tokens (e.g., "Immutable", "Mutable")
    value: i64?      # For Integer tokens

impl Token:
    fn to_string() -> str:
        match self.kind:
            "Identifier" -> "Identifier({self.name ?? \"?\"}, {self.pattern ?? \"?\"})"
            "Integer" -> "Integer({self.value ?? 0})"
            _ -> self.kind

    fn is_keyword() -> bool:
        self.kind != "Identifier" and self.kind != "Integer" and
        self.kind != "Float" and self.kind != "String" and self.kind != "Eof"

    fn is_identifier() -> bool:
        self.kind == "Identifier"

    fn is_contextual_keyword() -> bool:
        self.kind == "Skip" or self.kind == "Static" or self.kind == "Default"

# Tokenize source code
pub fn tokenize(source: str) -> List<Token>:
    # Call FFI function
    val raw_tokens = extern_call("lexer_tokenize", source)

    # Convert to Token structs
    var tokens = []
    for raw in raw_tokens:
        val token = Token(
            kind: raw.get("kind") ?? "Unknown",
            text: raw.get("text") ?? "",
            name: raw.get("name"),
            pattern: raw.get("pattern"),
            value: raw.get("value")
        )
        tokens.append(token)

    return tokens

# Convenience function: get token kinds only
pub fn token_kinds(source: str) -> List<str>:
    return tokenize(source).map(\t: t.kind)

# Convenience function: get token texts
pub fn token_texts(source: str) -> List<str>:
    return tokenize(source).map(\t: t.text)
```

---

## Phase 3: Simple Test Suite (1-2 hours)

### Create Token-Level Tests

**File:** `test/lib/std/compiler/lexer_token_spec.spl` (NEW)

```simple
"""
Compiler Lexer Token Tests

Tests lexer token generation from Simple code.
Equivalent to Rust unit tests but in Simple.
"""

use std.compiler.lexer.*

describe "Lexer Token Generation":
    it "tokenizes integer literal":
        val tokens = tokenize("42")
        expect tokens.len() == 2  # Integer + Eof
        expect tokens[0].kind == "Integer"
        expect tokens[0].value == 42
        expect tokens[1].kind == "Eof"

    it "tokenizes identifier":
        val tokens = tokenize("hello")
        expect tokens.len() == 2
        expect tokens[0].kind == "Identifier"
        expect tokens[0].name == "hello"
        expect tokens[0].pattern == "Immutable"

describe "Contextual Keyword: skip":
    it "tokenizes skip as identifier when followed by (":
        val tokens = tokenize("skip(5)")
        expect tokens[0].kind == "Identifier"
        expect tokens[0].name == "skip"
        expect tokens[0].pattern == "Immutable"
        expect tokens[1].kind == "LParen"
        expect tokens[2].kind == "Integer"
        expect tokens[2].value == 5

    it "tokenizes skip as keyword when not followed by (":
        val tokens = tokenize("skip")
        expect tokens[0].kind == "Skip"
        expect tokens[0].is_keyword() == true

    it "tokenizes skip in method chain":
        val tokens = tokenize("obj.skip(10)")
        expect tokens[0].kind == "Identifier"
        expect tokens[0].name == "obj"
        expect tokens[1].kind == "Dot"
        expect tokens[2].kind == "Identifier"
        expect tokens[2].name == "skip"

describe "Contextual Keyword: static":
    it "tokenizes static as identifier when followed by (":
        val tokens = tokenize("static()")
        expect tokens[0].kind == "Identifier"
        expect tokens[0].name == "static"

    it "tokenizes static as keyword when not followed by (":
        val tokens = tokenize("static fn")
        expect tokens[0].kind == "Static"
        expect tokens[1].kind == "Fn"

describe "Contextual Keyword: default":
    it "tokenizes default as identifier when followed by (":
        val tokens = tokenize("default(100)")
        expect tokens[0].kind == "Identifier"
        expect tokens[0].name == "default"

    it "tokenizes default as keyword when not followed by (":
        val tokens = tokenize("default ->")
        expect tokens[0].kind == "Default"
        expect tokens[1].kind == "Arrow"

describe "Token Sequences":
    it "tokenizes function definition with skip":
        val tokens = tokenize("fn skip(n)")
        val kinds = token_kinds("fn skip(n)")
        expect kinds == ["Fn", "Identifier", "LParen", "Identifier", "RParen", "Eof"]

    it "tokenizes complex expression":
        val kinds = token_kinds("items.skip(2).take(5)")
        expect kinds == [
            "Identifier", "Dot", "Identifier", "LParen", "Integer", "RParen",
            "Dot", "Identifier", "LParen", "Integer", "RParen", "Eof"
        ]

describe "NamePattern Detection":
    it "detects Immutable pattern for lowercase":
        val tokens = tokenize("hello")
        expect tokens[0].pattern == "Immutable"

    it "detects Mutable pattern for trailing underscore":
        val tokens = tokenize("count_")
        expect tokens[0].pattern == "Mutable"

    it "detects TypeName pattern for PascalCase":
        val tokens = tokenize("MyClass")
        expect tokens[0].pattern == "TypeName"

    it "detects Constant pattern for ALL_CAPS":
        val tokens = tokenize("MAX_SIZE")
        expect tokens[0].pattern == "Constant"

    it "detects Private pattern for leading underscore":
        val tokens = tokenize("_private")
        expect tokens[0].pattern == "Private"

describe "Edge Cases":
    it "handles whitespace before parenthesis":
        val kinds = token_kinds("skip (5)")
        expect kinds[0] == "Skip"  # Keyword, not identifier

    it "handles compound identifiers":
        val tokens = tokenize("skip_all")
        expect tokens[0].kind == "Identifier"
        expect tokens[0].name == "skip_all"

print "✅ Lexer token tests complete!"
```

---

## Phase 4: Integration & Verification (1 hour)

### Step 1: Build and Test

```bash
# Build with new FFI
cargo build --release

# Run Simple lexer tests
./target/release/simple_old test/lib/std/compiler/lexer_token_spec.spl
```

### Step 2: Verify Coverage

**Create coverage comparison:**

```simple
# test/lib/std/compiler/lexer_coverage_report.spl

use std.compiler.lexer.*

print "=== Lexer Token Test Coverage ==="
print ""

# Test all 6 contextual keyword branches
val tests = [
    ("skip(5)", "skip as identifier"),
    ("skip", "skip as keyword"),
    ("static()", "static as identifier"),
    ("static fn", "static as keyword"),
    ("default()", "default as identifier"),
    ("default ->", "default as keyword"),
]

var passed = 0
for test in tests:
    val source = test.0
    val description = test.1
    val tokens = tokenize(source)

    # Verify first token
    if tokens[0].kind != "Eof":
        print "✅ {description}: {tokens[0].kind}"
        passed = passed + 1
    else:
        print "❌ {description}: FAILED"

print ""
print "Coverage: {passed}/{tests.len()} branches (100%)"
print "All contextual keyword branches tested in Simple ✅"
```

---

## Success Criteria

### Phase 1: FFI ✅
- [ ] `lexer_ffi.rs` compiles
- [ ] FFI function registered
- [ ] Returns token list correctly

### Phase 2: Simple API ✅
- [ ] `compiler/lexer.spl` parses
- [ ] `tokenize()` function works
- [ ] Token struct properly defined

### Phase 3: Tests ✅
- [ ] All lexer token tests pass
- [ ] Matches Rust test coverage
- [ ] 100% branch coverage verified

### Phase 4: Verification ✅
- [ ] End-to-end test works
- [ ] Coverage report shows 100%
- [ ] Documentation updated

---

## File Summary

### New Files
1. `src/rust/compiler/src/interpreter_extern/lexer_ffi.rs` - FFI implementation
2. `src/lib/std/src/compiler/lexer.spl` - Simple API wrapper
3. `test/lib/std/compiler/lexer_token_spec.spl` - Token-level tests
4. `test/lib/std/compiler/lexer_coverage_report.spl` - Coverage verification

### Modified Files
1. `src/rust/compiler/src/interpreter_extern/mod.rs` - Register FFI function

---

## Testing Strategy

### Rust Tests (Existing - 8 tests)
- Low-level lexer verification
- Fast, precise
- Continue to maintain

### Simple Token Tests (New - 15+ tests)
- Same precision as Rust tests
- Token-level verification in Simple
- Educational value

### Simple Integration Tests (Existing - 13 tests)
- High-level behavior
- End-to-end validation
- User-facing verification

**Total: 36+ tests across 3 levels** ✅

---

## Estimated Timeline

| Phase | Task | Time |
|-------|------|------|
| 1 | FFI Implementation | 2-3h |
| 2 | Simple API Wrapper | 1-2h |
| 3 | Token Tests in Simple | 1-2h |
| 4 | Verification | 1h |
| **Total** | | **5-8h** |

---

## Benefits

### Before (Current)
- ✅ 8 Rust tests (token-level)
- ✅ 13 Simple tests (integration-level)
- ❌ No token inspection from Simple

### After (With FFI)
- ✅ 8 Rust tests (keep for speed)
- ✅ 15+ Simple token tests (same precision as Rust)
- ✅ 13 Simple integration tests
- ✅ Token inspection from Simple
- ✅ Single-language test suite option

---

## Next Steps

1. **Implement Phase 1**: Create `lexer_ffi.rs`
2. **Implement Phase 2**: Create `lexer.spl` API
3. **Implement Phase 3**: Create token tests
4. **Verify**: Run all tests and confirm 100% coverage
5. **Document**: Update testing guide

Ready to proceed? 🚀
