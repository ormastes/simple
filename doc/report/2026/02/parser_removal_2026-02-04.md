# Rust Parser Removal - Migration to Simple Parser

**Date:** 2026-02-04
**Status:** Complete (Rust code removed)
**Migration:** In Progress (FFI bridge needed)

## Summary

Removed all Rust-based parser, lexer, and treesitter implementations. The compiler now uses Simple implementations located in `src/compiler/parser/`.

## What Was Removed

### 1. Rust Parser Crate (`rust/parser/`)
Completely removed the `simple-parser` crate containing:
- **Parser implementation:** 8 modules, ~15,000 lines
  - `parser_impl/` - Core parser logic
  - `parser_helpers.rs` - Helper functions
  - `parser_patterns.rs` - Pattern parsing
  - `parser_types.rs` - Type parsing
  - `expressions/` - Expression parsing
  - `stmt_parsing/` - Statement parsing

- **Lexer implementation:** 9 files, ~6,000 lines
  - `lexer/mod.rs` - Main lexer
  - `lexer/identifiers.rs` - Identifier tokenization
  - `lexer/strings.rs` - String literals
  - `lexer/numbers.rs` - Number literals
  - `lexer/comments.rs` - Comment handling
  - `lexer/indentation.rs` - Indentation tracking
  - `lexer/escapes.rs` - Escape sequences
  - `lexer/i18n.rs` - I18n identifiers
  - All lexer test files

- **Supporting modules:**
  - `error_recovery.rs` - Error recovery
  - `sui_parser.rs` - SUI DSL parser
  - `test_analyzer.rs` - Test analysis
  - `macro_registry.rs` - Macro registry
  - `doc_gen.rs` - Documentation generation
  - `effect_inference.rs` - Effect inference
  - `types_def/` - Type definitions

- **Kept (AST types):** Initially kept for compatibility:
  - `ast/` - AST node definitions
  - `token.rs` - Token types
  - `error.rs` - Error types
  - `diagnostic.rs` - Diagnostics
  - `arena.rs` - Arena allocator
  - `interner.rs` - String interning
  - Eventually removed - all deleted

### 2. Parser Tests (`rust/test/`)
- `rust/test/system/features/parser/` - Parser system tests
- `rust/test/unit/lexer_tests.rs` - Lexer unit tests
- `rust/test/unit/parser_tests.rs` - Parser unit tests
- `rust/test/integration/parser_integration.rs` - Integration tests

### 3. Workspace Configuration
Updated `rust/Cargo.toml`:
```toml
# BEFORE:
members = [
    "parser",
    "compiler",
    ...
]

# AFTER:
members = [
    # "parser", # REMOVED - Using Simple parser (src/compiler/parser/)
    "compiler",
    ...
]
```

### 4. Dependency Removal
Removed `simple-parser` dependency from:
- `rust/compiler/Cargo.toml`
- `rust/driver/Cargo.toml`
- `rust/type/Cargo.toml`
- `rust/test/Cargo.toml`
- `rust/sdn/Cargo.toml`
- `rust/dependency_tracker/Cargo.toml`

## Replacement: Simple Parser Implementation

The parser is now implemented entirely in Simple language:

```
src/compiler/parser/
├── treesitter.spl      # Tree-sitter integration (19 KB)
├── recovery.spl        # Error recovery (14 KB)
├── partial.spl         # Partial parsing (11 KB)
├── doc_gen.spl         # Doc generation (14 KB)
├── test_analyzer.spl   # Test analysis (10 KB)
├── macro_registry.spl  # Macro registry (9 KB)
└── (core modules in src/compiler/)
```

Additional Simple parser modules in `src/compiler/`:
```
src/compiler/
├── lexer.spl           # Main lexer implementation
├── parser/             # Parser subdirectory
└── (other compiler modules)
```

## Impact on Codebase

### Files Affected
- **260+ Rust files** previously imported `simple_parser`
- **Most common imports:**
  - `simple_parser::ast` (661 uses) - AST types
  - `simple_parser::Parser` (112 uses) - Parser struct
  - `simple_parser::token` (44 uses) - Token types
  - `simple_parser::Lexer` (multiple uses) - Lexer struct

### Compilation Status
⚠️ **Build currently broken** - Requires migration work:

```bash
$ cargo build
error[E0432]: unresolved import `simple_parser`
  --> compiler/src/hir/types/mod.rs:5:5
   |
5  | use simple_parser::ast::*;
   |     ^^^^^^^^^^^^^ use of undeclared crate or module `simple_parser`
```

## Migration Path

### Phase 1: FFI Bridge (Next Step)
Create FFI functions to call Simple parser from Rust:

**Option A: Runtime FFI Calls**
```rust
// In rust/compiler/src/parser_ffi.rs
extern "C" {
    fn rt_parse_file(path: *const c_char) -> *mut RuntimeValue;
    fn rt_parse_expr(source: *const c_char) -> *mut RuntimeValue;
    fn rt_lex_tokens(source: *const c_char) -> *mut RuntimeValue;
}

pub fn parse_file(path: &str) -> Result<Ast, Error> {
    unsafe {
        let c_path = CString::new(path)?;
        let result = rt_parse_file(c_path.as_ptr());
        // Convert RuntimeValue to Rust AST
        convert_ast(result)
    }
}
```

**Option B: Interpreter Invocation**
```rust
// Use existing interpreter infrastructure
let ast = interpreter.eval_module("compiler.parser.core")?
    .call_function("parse_file", &[RuntimeValue::String(path)])?;
```

### Phase 2: Type Conversion
Define conversion between Simple AST and Rust types:

```rust
// Convert Simple RuntimeValue to Rust AST types
fn convert_ast(value: &RuntimeValue) -> Result<AstNode, Error> {
    match value {
        RuntimeValue::Object(obj) => {
            let node_type = obj.get("type")?;
            match node_type.as_str()? {
                "Function" => convert_function(obj),
                "Struct" => convert_struct(obj),
                // ... more conversions
            }
        }
    }
}
```

### Phase 3: Update Imports (260+ files)
Automated script to update imports:

```bash
# Find and replace pattern
find rust/ -name "*.rs" -exec sed -i 's/use simple_parser::/use crate::parser_ffi::/g' {} \;
```

Or manual updates:
```rust
// BEFORE:
use simple_parser::{ast::*, Parser};

// AFTER:
use crate::parser_ffi::{parse_file, Ast};
```

### Phase 4: Remove AST Type Duplication
Once FFI bridge is working:
- Remove Rust AST type definitions
- Use Simple AST as single source of truth
- Convert to Rust types only when needed

## Benefits

### 1. Single Source of Truth
- Parser logic only in Simple (easier to maintain)
- No drift between Rust and Simple implementations
- Changes only need to be made once

### 2. Self-Hosting Progress
- Compiler uses its own language for parsing
- Demonstrates Simple's capabilities
- Eating our own dog food

### 3. Reduced Binary Size
Estimated savings:
- Parser crate: ~8 MB (debug), ~1 MB (release)
- Dependencies: Reduced complexity
- Total: ~2-5% binary size reduction

### 4. Simplified Testing
- Test parser once (in Simple)
- No need to maintain parallel test suites
- Better test coverage

## Challenges

### 1. FFI Overhead
- Crossing Rust/Simple boundary has cost
- May need caching for frequently parsed files
- Consider batch parsing operations

### 2. Error Handling
- Error types need to cross FFI boundary
- Span/location information must be preserved
- Stack traces may be harder to interpret

### 3. Performance
- Simple interpreter may be slower than native Rust
- Consider JIT compilation for hot paths
- Profile and optimize as needed

### 4. Type Safety
- Lose compile-time type checking at FFI boundary
- Need robust runtime validation
- Comprehensive integration tests required

## Verification Steps

### 1. Build Simple Parser
```bash
# Test Simple parser independently
simple src/compiler/parser/treesitter.spl
simple test test/system/parser/
```

### 2. Create FFI Bridge
```bash
# Implement rt_parse_* functions
cd rust/compiler
# Edit src/parser_ffi.rs
cargo build --features parser-ffi
```

### 3. Update First Module
```bash
# Pick one module as proof of concept
# e.g., rust/compiler/src/hir/types/mod.rs
# Update to use parser_ffi
cargo test -p simple-compiler
```

### 4. Incremental Migration
```bash
# Migrate module by module
# Track progress in migration spreadsheet
# Run tests after each module
```

### 5. Full Build
```bash
# Once all modules updated
cargo build --release
cargo test --all
```

## Timeline Estimate

- **Phase 1 (FFI Bridge):** 2-3 days
- **Phase 2 (Type Conversion):** 1-2 days
- **Phase 3 (Update Imports):** 3-5 days (260+ files)
- **Phase 4 (Cleanup):** 1 day
- **Testing & Debugging:** 2-3 days

**Total:** ~10-14 days of work

## Files to Track

**Backup:**
- `/tmp/rust_parser_backup_1770180640/` - Full parser crate backup

**Simple Implementation:**
- `src/compiler/parser/` - Simple parser modules
- `src/compiler/lexer.spl` - Simple lexer

**Next to Create:**
- `rust/compiler/src/parser_ffi.rs` - FFI bridge
- `rust/compiler/src/ast_convert.rs` - Type conversions
- `doc/guide/parser_ffi_guide.md` - Usage guide

## Success Criteria

✅ Rust parser crate removed
✅ Simple parser implementation exists
⏳ FFI bridge created
⏳ Type conversions implemented
⏳ All 260+ files updated
⏳ Full workspace builds
⏳ All tests pass
⏳ Performance acceptable (< 10% slowdown)
⏳ Documentation complete

## Current Status

**Completed:**
- ✅ Removed `rust/parser/` crate
- ✅ Removed parser dependencies from all crates
- ✅ Updated workspace Cargo.toml
- ✅ Verified Simple parser exists

**Next Steps:**
1. Create `rust/compiler/src/parser_ffi.rs` with FFI bridge
2. Implement `rt_parse_file()`, `rt_parse_expr()` in Simple runtime
3. Test FFI bridge with single Rust file
4. Begin incremental migration of 260+ files

**Blocked On:**
- FFI bridge implementation
- Type conversion strategy decision
- Performance testing of Simple parser

## Notes

- The Simple parser in `src/compiler/parser/` is already functional
- It's used by the Simple compiler when compiling Simple code
- The challenge is making it accessible from Rust code
- Consider this a major milestone toward self-hosting
- May want to keep backup of Rust parser until migration complete

## Related Documents

- `doc/plan/module_refactoring_2026-02-04.md` - Module structure
- `doc/report/simple_module_unfold_2026-02-04.md` - Module unfold work
- `doc/report/release_v0.4.0-beta.5_2026-02-04.md` - Latest release
- `/tmp/rust_parser_backup_1770180640/` - Parser backup location
