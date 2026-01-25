# Module Sharing Design

## Overview

This document describes the target architecture for sharing logic between compiler, interpreter, SDN parser, and TreeSitter.

---

## Current State

```
┌─────────────────────────────────────────────────────────────────┐
│                    SIMPLE PROGRAMS (.spl)                        │
│  sdn/main.spl, cli/main.spl, app/*.spl                          │
│                          │                                       │
│                          ▼                                       │
│              extern fn rt_* (FFI calls)                          │
└──────────────────────────┼───────────────────────────────────────┘
                           │
┌──────────────────────────▼───────────────────────────────────────┐
│                    RUST FFI LAYER                                │
│  sdn_ffi.rs, cli_ffi.rs, time.rs, etc.                          │
│                          │                                       │
│                          ▼                                       │
│              simple-runtime (RuntimeValue)                       │
└──────────────────────────┼───────────────────────────────────────┘
                           │
┌──────────────────────────▼───────────────────────────────────────┐
│                    RUST CORE (ISOLATED)                          │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────────────────┐ │
│  │compiler │  │ parser  │  │   sdn   │  │ hir-core (UNUSED)   │ │
│  │ Value   │  │  AST    │  │ SdnValue│  │ StructLayout        │ │
│  │ (own)   │  │  (own)  │  │  (own)  │  │ LogLevel            │ │
│  └─────────┘  └─────────┘  └─────────┘  └─────────────────────┘ │
│       ▲              ▲            ▲                              │
│       └──────────────┴────────────┘                              │
│              NO SHARED TYPES                                     │
└──────────────────────────────────────────────────────────────────┘
```

**Problems:**
- Compiler's `Value` and Runtime's `RuntimeValue` have separate layouts
- No shared log levels between modules
- SDN parser duplicates value types
- TreeSitter would need its own AST types
- No unified configuration/DI

---

## Target State

```
┌─────────────────────────────────────────────────────────────────┐
│                    SIMPLE PROGRAMS (.spl)                        │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  std_lib/src/                                               ││
│  │  ├── log.spl      (logging with levels 0-10)               ││
│  │  ├── db.spl       (SDN-backed tables)                      ││
│  │  ├── config.spl   (DI/configuration)                       ││
│  │  └── parse.spl    (parser utilities)                       ││
│  └─────────────────────────────────────────────────────────────┘│
│                          │                                       │
│                          ▼                                       │
│              extern fn rt_* (FFI calls)                          │
└──────────────────────────┼───────────────────────────────────────┘
                           │
┌──────────────────────────▼───────────────────────────────────────┐
│                    RUST FFI LAYER                                │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  simple-runtime/src/value/                                  ││
│  │  ├── sdn_ffi.rs   (SDN operations)                         ││
│  │  ├── cli_ffi.rs   (CLI operations)                         ││
│  │  ├── log_ffi.rs   (logging FFI) ◄── NEW                    ││
│  │  ├── db_ffi.rs    (database FFI) ◄── NEW                   ││
│  │  └── parse_ffi.rs (parser FFI) ◄── NEW                     ││
│  └─────────────────────────────────────────────────────────────┘│
│                          │                                       │
│                          ▼                                       │
│              simple-runtime (RuntimeValue)                       │
│              uses simple-hir-core                                │
└──────────────────────────┼───────────────────────────────────────┘
                           │
┌──────────────────────────▼───────────────────────────────────────┐
│                    SHARED CORE (simple-hir-core)                 │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  LogLevel        (0-10 levels, shared by all)               ││
│  │  StructLayout    (field offsets, sizes, alignment)          ││
│  │  EnumLayout      (variant tags, payloads)                   ││
│  │  FieldLayout     (individual field info)                    ││
│  │  HighLevelOp     (TypeAssert, CapabilityCheck, etc.)        ││
│  │  ValueKind       (shared value type enum)                   ││
│  │  TokenKind       (shared token types for parser/treesitter) ││
│  └─────────────────────────────────────────────────────────────┘│
│                          │                                       │
│          ┌───────────────┼───────────────┬───────────────┐       │
│          ▼               ▼               ▼               ▼       │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌───────────┐  │
│  │  compiler   │ │   parser    │ │     sdn     │ │treesitter │  │
│  │  uses       │ │   uses      │ │   uses      │ │  uses     │  │
│  │  hir-core   │ │   hir-core  │ │   hir-core  │ │  hir-core │  │
│  └─────────────┘ └─────────────┘ └─────────────┘ └───────────┘  │
└──────────────────────────────────────────────────────────────────┘
```

---

## Shared Types in hir-core

### 1. LogLevel (0-10)

```rust
// src/rust/hir-core/src/lib.rs
pub enum LogLevel {
    Off = 0,      // No logging
    Fatal = 1,    // Unrecoverable
    Error = 2,    // Recoverable errors
    Warn = 3,     // Potential issues
    Info = 4,     // High-level events
    Debug = 5,    // Detailed events
    Trace = 6,    // Very detailed
    Verbose = 7,  // Every instruction
    All = 10,     // Everything
}
```

**Used by:**
- `simple-compiler` - Compilation diagnostics
- `simple-runtime` - Runtime logging
- `simple-parser` - Parse diagnostics
- `simple-sdn` - SDN parse errors
- `log.spl` - Simple logging module

### 2. Layout Types

```rust
// Shared between compiler's Value and runtime's RuntimeValue
pub struct StructLayout {
    pub name: String,
    pub size: usize,
    pub align: usize,
    pub fields: Vec<FieldLayout>,
}

pub struct EnumLayout {
    pub name: String,
    pub tag_size: usize,
    pub variants: Vec<VariantLayout>,
}
```

**Used by:**
- `simple-compiler` - Interpreter's `Value` layout
- `simple-runtime` - `RuntimeValue` layout
- Code generation - Memory allocation

### 3. Token Types (for parser/treesitter sharing)

```rust
// Shared token types
pub enum TokenKind {
    // Literals
    IntLit, FloatLit, StringLit, BoolLit,
    // Keywords
    KwFn, KwVal, KwVar, KwIf, KwElse, KwMatch, KwFor, KwWhile,
    KwStruct, KwClass, KwEnum, KwTrait, KwImpl,
    // Operators
    Plus, Minus, Star, Slash, Percent,
    Eq, EqEq, Ne, Lt, Le, Gt, Ge,
    // Delimiters
    LParen, RParen, LBrace, RBrace, LBracket, RBracket,
    Comma, Colon, Semicolon, Arrow, FatArrow,
    // Special
    Ident, Comment, Whitespace, Newline, Eof,
}
```

**Used by:**
- `simple-parser` - Lexer token output
- `simple-sdn` - SDN lexer tokens
- TreeSitter grammar - Token definitions
- LSP - Syntax highlighting

### 4. Value Kind (shared value representation)

```rust
// Abstract value types shared by interpreter and compiler
pub enum ValueKind {
    Int,
    Float,
    Bool,
    String,
    Array,
    Dict,
    Struct { layout: StructLayout },
    Enum { layout: EnumLayout },
    Function,
    Closure,
    None,
}
```

**Used by:**
- `simple-compiler` - Interpreter `Value` enum
- `simple-runtime` - `RuntimeValue` type tags
- Type checker - Type representation

### 5. High-Level Operations

```rust
// Constraint operations understood by both interpreter and compiled code
pub enum HighLevelOp {
    TypeAssert { expected: String },
    CapabilityCheck { capability: String },
    EffectBoundary { effect: String },
    Precondition { condition: String },
    Postcondition { condition: String },
    Invariant { condition: String },
}
```

**Used by:**
- `simple-compiler` - Contract checking in interpreter
- Code generation - Insert runtime checks
- Lean verification - Formal property verification

---

## Crate Dependency Graph (Target)

```
                    simple-hir-core
                          │
        ┌─────────────────┼─────────────────┐
        │                 │                 │
        ▼                 ▼                 ▼
  simple-parser     simple-sdn      simple-runtime
        │                 │                 │
        └────────┬────────┘                 │
                 │                          │
                 ▼                          │
          simple-compiler ◄─────────────────┘
                 │
                 ▼
           simple-driver
```

### Cargo.toml Changes Required

```toml
# src/rust/parser/Cargo.toml
[dependencies]
simple-hir-core = { path = "../hir-core" }

# src/rust/sdn/Cargo.toml
[dependencies]
simple-hir-core = { path = "../hir-core" }

# src/rust/runtime/Cargo.toml
[dependencies]
simple-hir-core = { path = "../hir-core" }

# src/rust/compiler/Cargo.toml
[dependencies]
simple-hir-core = { path = "../hir-core" }
```

---

## FFI Mapping (Simple ↔ Rust)

### Logging FFI

```
Simple (log.spl)              Rust (log_ffi.rs)
────────────────              ─────────────────
log.fatal(scope, msg)    →    rt_log_emit(1, scope, msg)
log.error(scope, msg)    →    rt_log_emit(2, scope, msg)
log.warn(scope, msg)     →    rt_log_emit(3, scope, msg)
log.info(scope, msg)     →    rt_log_emit(4, scope, msg)
log.debug(scope, msg)    →    rt_log_emit(5, scope, msg)
log.set_level(n)         →    rt_log_set_global_level(n)
log.get_level(scope)     →    rt_log_get_level(scope)
```

### Database FFI

```
Simple (db.spl)               Rust (db_ffi.rs)
────────────────              ─────────────────
Table.load(path)         →    rt_db_load(path)
table.save()             →    rt_db_save(path, content)
table.filter(pred)       →    (Simple-only, no FFI)
table.to_markdown()      →    (Simple-only, no FFI)
```

### Parser FFI (for outline mode)

```
Simple (parse.spl)            Rust (parse_ffi.rs)
──────────────────            ──────────────────
parse_outline(source)    →    rt_parse_outline(source)
parse_full(source)       →    rt_parse_full(source)
get_tokens(source)       →    rt_tokenize(source)
```

---

## Implementation Phases

### Phase 1: Connect hir-core (COMPLETE)
- [x] Create `simple-hir-core` crate
- [x] Add LogLevel, StructLayout, EnumLayout
- [x] Link to `simple-compiler`
- [x] Link to `simple-runtime`
- [x] Link to `simple-parser`
- [x] Link to `simple-sdn`
- [x] Link to `simple-diagnostics`
- [x] Create `config.spl` (374 lines)
- [x] Create `di.spl` (423 lines)

### Phase 2: Add log FFI
- [ ] Implement `log_ffi.rs` in runtime
- [ ] Connect `log.spl` to FFI
- [ ] Use LogLevel from hir-core

### Phase 3: Add TokenKind sharing
- [ ] Add TokenKind to hir-core
- [ ] Refactor parser to use shared TokenKind
- [ ] Refactor SDN lexer to use shared TokenKind
- [ ] Prepare for TreeSitter integration

### Phase 4: Add ValueKind sharing
- [ ] Add ValueKind to hir-core
- [ ] Refactor compiler's Value to use shared layout
- [ ] Refactor runtime's RuntimeValue to use shared layout

### Phase 5: Parser outline mode
- [ ] Add `parse_outline()` to parser
- [ ] Expose via FFI
- [ ] Create `parse.spl` Simple module

---

## Size Targets

| Module | Current (Rust) | Actual (Simple) | Target | Reduction |
|--------|----------------|-----------------|--------|-----------|
| log | (none) | 143 lines | 143 | n/a |
| db | 2930 lines | 251 lines | 251 | 91% |
| config | ~500 lines | 374 lines | 150 | 25% |
| di | ~400 lines | 423 lines | 80 | -6% |
| time | (in runtime) | 129 lines | 130 | n/a |
| map | (in runtime) | 475 lines | - | n/a |
| set | (in runtime) | 479 lines | - | n/a |
| parse utils | (in parser) | ~200 (TODO) | 200 | n/a |

**Current Simple stdlib**: 2,274 lines (7 modules)
**Shared Rust core (hir-core)**: ~500 lines

**Note**: config.spl and di.spl are larger than target because they include
full type definitions that will be shared. When types are extracted to a
common module, the size will be reduced.

---

## Benefits

1. **Single source of truth** for layout types
2. **Consistent logging** across all modules (0-10 levels)
3. **TreeSitter compatibility** via shared TokenKind
4. **Smaller Simple code** by leveraging FFI for heavy lifting
5. **Type-safe FFI** via shared type definitions
6. **Formal verification ready** with shared HighLevelOp
