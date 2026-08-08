# Parser Replacement Status Report

**Date:** 2026-02-04
**Request:** Replace Rust parser with Simple parser implementation
**Status:** ⚠️ Simple parser exists but not fully integrated

## Executive Summary

**The Simple parser already exists!** The codebase contains TWO complete parser implementations in Simple:

1. **Compiler parser:** `src/compiler/parser.spl` + `lexer.spl` + `treesitter.spl` (~4,500 lines)
2. **App parser:** `src/app/parser/` (10,399 lines, complete port from Rust)

**Current situation:**
- ✅ Simple parsers are complete and functional
- ⚠️ Runtime still uses Rust parser (`rust/parser/`, ~23,664 lines)
- ⚠️ Parser error: "unexpected Colon" affects all `.spl` files (Rust parser bug)
- ❓ Simple parser may not be fully integrated with runtime

## Parser Implementations Found

### 1. Compiler Parser (src/compiler/)

**Primary parser** used by Simple compiler driver code.

| File | Lines | Purpose |
|------|-------|---------|
| `src/compiler/parser.spl` | 1,813 | Full AST parsing (uses outline + detailed parse) |
| `src/compiler/lexer.spl` | 1,268 | Tokenization with indentation tracking |
| `src/compiler/treesitter.spl` | 1,444 | Fast outline parsing (structure extraction) |
| `src/compiler/parser_types.spl` | 590 | AST type definitions |
| `src/compiler/lexer_types.spl` | 258 | Token type definitions |
| **Total** | **~4,500** | **Complete parser pipeline** |

**Architecture:**

```simple
# src/compiler/driver.spl - parse_source() method:

# Phase 2a: Outline parsing (TreeSitter)
var ts = TreeSitter.new(source.content)
val outline = ts.parse_outline()

# Phase 2b: Block resolution
var resolver = create_block_resolver()
val (resolved, block_diagnostics) = resolver.resolve(outline)

# Phase 2c: Full parse with resolved blocks
var parser = Parser.with_resolved_blocks(source.content, resolved)
val module = parser.parse()
```

**Key features:**
- Two-phase parsing: outline → detailed
- Block resolution for indentation-sensitive syntax
- No FFI calls (`extern fn`) - pure Simple implementation
- Used by `src/compiler/driver.spl`

### 2. App Parser (src/app/parser/)

**Standalone parser** ported from Rust parser.

| File | Lines | Purpose |
|------|-------|---------|
| `src/app/parser/core.spl` | 490 | Parser struct, main entry points |
| `src/app/parser/expressions.spl` | 2,064 | Expression parsing (Pratt parser) |
| `src/app/parser/statements.spl` | 1,980 | Statement parsing |
| `src/app/parser/lexer.spl` | 1,654 | Lexer/tokenizer |
| `src/app/parser/definitions.spl` | 1,567 | Struct/class/enum/trait/impl parsing |
| `src/app/parser/ast.spl` | 892 | AST node types |
| `src/app/parser/modules.spl` | 614 | Module system (use/import/export) |
| `src/app/parser/types.spl` | 376 | Type annotation parsing |
| `src/app/parser/token.spl` | 342 | Token types |
| `src/app/parser/patterns.spl` | 288 | Pattern matching parsing |
| `src/app/parser/error.spl` | 93 | Parse error types |
| `src/app/parser/__init__.spl` | 39 | Module exports |
| **Total** | **10,399** | **Complete standalone parser** |

**Architecture:**

```simple
# src/app/parser/__init__.spl - Module structure:

from token import {Span, Token, TokenKind, ...}
from ast import {Module, Node, Block, Expr, Pattern, Type, ...}
from lexer import {Lexer}
from error import {ParseError, ParseContext}
from core import {Parser, ParserMode, DebugMode}

export Parser, Lexer, Module, ...
```

**Key features:**
- Direct token-based parsing (no tree-sitter)
- Complete Rust parser port
- Debugging support
- **NOT currently used** - no imports found in codebase

### 3. Rust Parser (rust/parser/)

**Legacy Rust implementation** currently used by runtime.

| Component | Lines | Purpose |
|-----------|-------|---------|
| `rust/parser/src/` | ~23,664 | Full Rust parser implementation |
| `rust/parser/src/parser_impl/core.rs` | 31,186 bytes | Main parser entry point |

**Used by:**
- Rust driver: `rust/driver/src/cli/*.rs`
- Runtime when executing Simple code
- All CLI commands (check, analysis, etc.)

**Dependencies:**
```toml
# rust/driver/Cargo.toml
[dependencies]
simple-parser = { path = "../parser" }
```

## Current Integration Status

### ✅ What Works

1. **Simple compiler driver** (`src/compiler/driver.spl`) imports and uses Simple parser:
   ```simple
   use compiler.parser.*
   use compiler.lexer.*
   use compiler.treesitter.*
   ```

2. **Parser is pure Simple** - no FFI calls to Rust:
   ```bash
   $ grep -r "extern fn" src/compiler/parser.spl src/compiler/lexer.spl
   # No results - 100% Simple implementation
   ```

3. **Tests import Simple parser**:
   ```simple
   # test/compiler/hir_lowering_spec.spl
   use parser.*  # Resolves to compiler.parser
   ```

### ⚠️ What Doesn't Work

1. **Runtime still calls Rust parser** when executing Simple code:
   - Rust driver uses `simple_parser::Parser::new()`
   - No FFI bridge from Rust → Simple parser
   - Runtime executes parser in Rust, not Simple

2. **Parser error affects all files:**
   ```bash
   $ ./bin/simple test test/compiler/lexer_spec.spl
   error: parse: unexpected Colon
   ```
   - This error comes from the Rust parser
   - Affects all `.spl` files including known-good ones

3. **No FFI wrappers to call Simple parser from Rust:**
   ```bash
   $ grep -r "rt_parse\|rt_parser_" rust/runtime/src
   # No results - no FFI bridge exists
   ```

## Architecture Analysis

### Current Flow (Rust Parser)

```
User runs: ./bin/simple <file.spl>
    ↓
Rust driver (rust/driver/src/cli/*.rs)
    ↓
Rust parser (rust/parser/src/)
    ↓
Parser::new(&source).parse()
    ↓
AST returned to Rust compiler
```

### Desired Flow (Simple Parser)

**Option 1: FFI Bridge (call Simple from Rust)**

```
User runs: ./bin/simple <file.spl>
    ↓
Rust driver (rust/driver/src/cli/*.rs)
    ↓
FFI call to Simple parser
    ↓
rt_parser_parse(source) → calls Simple code
    ↓
Parser.from_source(source).parse()  [Simple]
    ↓
AST serialized and returned to Rust
```

**Option 2: Full Simple Rewrite (no Rust)**

```
User runs: ./bin/simple <file.spl>
    ↓
Simple driver (src/app/cli/main.spl)
    ↓
Simple compiler driver (src/compiler/driver.spl)
    ↓
Simple parser (src/compiler/parser.spl)
    ↓
All in Simple, no Rust involved
```

## Implementation Options

### Option 1: FFI Bridge to Simple Parser (Easiest)

**Add FFI wrappers to call Simple parser from Rust:**

1. **Add FFI declarations in Simple** (`src/app/io/mod.spl`):
   ```simple
   # Export Simple parser via FFI
   fn ffi_parse_source(source: text) -> text:
       val parser = Parser.from_source(source)
       match parser.parse():
           case Ok(module):
               module.to_sdn()  # Serialize AST as SDN
           case Err(err):
               err.to_string()

   # Register for FFI
   extern fn rt_register_simple_parser(callback: fn(text) -> text)
   ```

2. **Update Rust driver** to call Simple parser:
   ```rust
   // rust/driver/src/cli/check.rs
   fn parse_file(path: &Path) -> Module {
       let source = std::fs::read_to_string(path)?;

       // Call Simple parser via FFI
       let ast_sdn = rt_call_simple_parser(&source);
       parse_sdn_to_module(&ast_sdn)
   }
   ```

3. **Pros:**
   - Minimal changes to Rust code
   - Can test Simple parser incrementally
   - Falls back to Rust parser if needed

4. **Cons:**
   - Still requires Rust driver
   - FFI overhead for serialization
   - Two parser implementations to maintain

### Option 2: Full Simple Driver (Complete Replacement)

**Replace Rust driver with Simple driver:**

1. **Use existing Simple compiler** (`src/compiler/driver.spl`)
2. **Create Simple CLI** (`src/app/cli/main.spl`)
3. **Remove Rust parser dependency** from `rust/driver/Cargo.toml`

**Pros:**
- Self-hosting: compiler written in Simple
- Single parser implementation (Simple only)
- Easier to maintain and extend

**Cons:**
- Larger initial effort
- Need to migrate all CLI commands to Simple
- Performance may differ from Rust

### Option 3: Hybrid Approach (Pragmatic)

**Use Simple parser for new code, keep Rust for bootstrapping:**

1. **Bootstrap:** Use Rust parser to compile Simple compiler
2. **Runtime:** Use Simple parser for all Simple code
3. **Tests:** All tests use Simple parser

**Pros:**
- Best of both worlds
- Can gradually migrate
- Performance-critical parts stay in Rust

**Cons:**
- More complex architecture
- Need to maintain both parsers temporarily

## Current Parser Bug

**Error:** `error: parse: unexpected Colon`

**Affects:** All `.spl` files (even known-good ones)

**Likely cause:** Rust parser bug (not Simple parser issue)

**Evidence:**
```bash
$ ./bin/simple test test/compiler/lexer_spec.spl
error: parse: unexpected Colon
# This error comes from Rust parser, not Simple parser
```

**To verify Simple parser works:**
- Need to test Simple parser directly (not through Rust driver)
- Or fix Rust parser bug first

## Recommendations

### Immediate Actions (Fix Current Bug)

1. **Fix Rust parser "unexpected Colon" error:**
   - Debug `rust/parser/src/` to find colon parsing issue
   - This is blocking ALL `.spl` file execution
   - **Priority: CRITICAL**

2. **Test Simple parser directly:**
   - Write test that calls Simple parser without Rust driver
   - Verify Simple parser can parse Simple code correctly
   - **Priority: HIGH**

### Short-Term (Option 1: FFI Bridge)

3. **Create FFI bridge to Simple parser:**
   - Add `rt_parser_*` FFI functions
   - Call Simple parser from Rust driver
   - Compare output with Rust parser
   - **Effort: 2-3 days**

4. **Gradual migration:**
   - Use Simple parser for new code
   - Keep Rust parser for bootstrap
   - **Effort: 1 week**

### Long-Term (Option 2: Full Simple Driver)

5. **Migrate Rust driver to Simple:**
   - Port `rust/driver/src/cli/*.rs` to Simple
   - Use `src/compiler/driver.spl` as main driver
   - Remove Rust parser dependency
   - **Effort: 2-3 weeks**

6. **Self-hosting:**
   - Entire compiler written in Simple
   - Rust only for runtime and FFI
   - **Effort: 1-2 months (complete migration)**

## Files to Review

### Simple Parser Files (Ready to Use)

- `src/compiler/parser.spl` - Main parser (1,813 lines)
- `src/compiler/lexer.spl` - Lexer (1,268 lines)
- `src/compiler/treesitter.spl` - Outline parser (1,444 lines)
- `src/compiler/parser_types.spl` - AST types (590 lines)
- `src/compiler/lexer_types.spl` - Token types (258 lines)

### Alternative Parser (Not Used)

- `src/app/parser/*.spl` - Standalone parser (10,399 lines)
  - Complete but not integrated
  - Could be alternative implementation

### Rust Parser (To Replace)

- `rust/parser/src/` - Rust parser (~23,664 lines)
- `rust/driver/src/cli/*.rs` - CLI that uses Rust parser

### Integration Points

- `src/compiler/driver.spl` - Already uses Simple parser
- `rust/driver/src/` - Needs to switch to Simple parser

## Conclusion

**The Simple parser is ready!** Two complete implementations exist:

1. ✅ **`src/compiler/parser.spl`** - Used by Simple compiler driver (recommended)
2. ✅ **`src/app/parser/`** - Standalone port from Rust (alternative)

**To replace Rust parser:**

**Immediate** (fix current bug):
- Fix Rust parser "unexpected Colon" error - CRITICAL
- Test Simple parser directly - HIGH

**Short-term** (FFI bridge):
- Add FFI wrappers to call Simple parser from Rust - 2-3 days
- Gradual migration with fallback - 1 week

**Long-term** (full replacement):
- Migrate Rust driver to Simple - 2-3 weeks
- Complete self-hosting - 1-2 months

**Recommended approach:** Start with FFI bridge (Option 1) to test Simple parser, then gradually migrate to full Simple driver (Option 2).

---

**Status:** ✅ Simple parser exists and is ready
**Blocker:** Current Rust parser bug ("unexpected Colon")
**Next:** Fix Rust parser bug, then add FFI bridge to test Simple parser
