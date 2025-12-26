# Compiler Pipeline Component Status

## Overview

The Simple language has two execution paths:
1. **Interpreter** (current): Tree-walking interpreter, fully featured
2. **Native Codegen** (TODO): HIR → MIR → Cranelift → Machine Code

## Current Execution Flow

```
Source (.spl)
    │
    ▼
┌─────────┐
│  Lexer  │  Status: COMPLETE
│ (parser)│  - Tokenization with INDENT/DEDENT
└────┬────┘  - Comments, line continuation
     │
     ▼
┌─────────┐
│ Parser  │  Status: COMPLETE
│ (parser)│  - Full AST generation
└────┬────┘  - All 48 original syntax features
     │
     ▼
┌──────────┐
│  Type    │  Status: PARTIAL
│ Checker  │  - HM-style unification
│  (type)  │  - Basic inference working
└────┬─────┘  - Runs before interpreter
     │
     ▼
┌───────────┐
│Interpreter│  Status: COMPLETE
│(compiler) │  - Tree-walking evaluation
│           │  - All language features
└────┬──────┘  - 425+ tests passing
     │
     ▼
┌─────────┐
│   SMF   │  Status: COMPLETE (wrapper only)
│ (loader)│  - Packages interpreter result
└────┬────┘  - `mov eax, <result>; ret`
     │
     ▼
┌─────────┐
│ Loader  │  Status: COMPLETE
│ (loader)│  - Memory-mapped execution
└─────────┘  - Symbol resolution
```

## Native Pipeline (TODO)

```
     AST
      │
      ▼
┌─────────┐
│   HIR   │  Status: STUB
│(compiler│  - Type structures exist
│ /hir)   │  - Lower module exists
└────┬────┘  - No real AST→HIR lowering
     │
     ▼
┌─────────┐
│   MIR   │  Status: STUB
│(compiler│  - Effect types defined
│ /mir)   │  - Block/instruction types
└────┬────┘  - No HIR→MIR transform
     │
     ▼
┌──────────┐
│Cranelift │  Status: STUB
│(compiler │  - Module structure exists
│/codegen) │  - Not wired to MIR
└──────────┘  - No real codegen
```

## Component Details

### Lexer (`src/parser/src/lexer.rs`)

| Feature | Status |
|---------|--------|
| Basic tokens | Complete |
| INDENT/DEDENT | Complete |
| Comments (#) | Complete |
| Line continuation (\\) | Complete |
| String interpolation | Complete |
| Numeric literals | Complete |

### Parser (`src/parser/src/parser.rs`)

| Feature | Status |
|---------|--------|
| Expressions | Complete |
| Statements | Complete |
| Functions/Classes | Complete |
| Pattern matching | Complete |
| Actors/spawn | Complete |
| Macros | Complete |

### Type Checker (`src/type/src/lib.rs`)

| Feature | Status |
|---------|--------|
| Type inference | Partial |
| Unification | Working |
| Substitution | Working |
| Occurs check | Working |
| Error reporting | Basic |

### Interpreter (`src/compiler/src/interpreter.rs`)

| Feature | Status |
|---------|--------|
| Expression eval | Complete |
| Statement exec | Complete |
| Functions/closures | Complete |
| Classes/structs | Complete |
| Pattern matching | Complete |
| Actors/concurrency | Complete |
| Macros | Complete |

### HIR (`src/compiler/src/hir/`)

| Feature | Status |
|---------|--------|
| Type definitions | Exists |
| Lowering module | Stub |
| AST→HIR transform | Not implemented |

### MIR (`src/compiler/src/mir/`)

| Feature | Status |
|---------|--------|
| Effect types | Complete (for verification) |
| Block/instruction types | Defined |
| HIR→MIR transform | Not implemented |

### Cranelift Codegen (`src/compiler/src/codegen/`)

| Feature | Status |
|---------|--------|
| Module structure | Exists |
| MIR→Cranelift | Not implemented |
| Function codegen | Not implemented |

### SMF Loader (`src/loader/`)

| Feature | Status |
|---------|--------|
| Binary format | Complete |
| Memory mapping | Complete |
| Symbol resolution | Complete |
| Execution | Complete |

### Runtime (`src/runtime/`)

| Feature | Status |
|---------|--------|
| GC wrapper (Abfall) | Complete |
| Actor spawner | Complete |
| Thread-local state | Complete |

## Test Distribution

```
Total: 425+ passing, 19 failing

By crate:
├── simple-parser:   ~180 tests
├── simple-driver:   ~100 tests (interpreter)
├── simple-type:     ~22 tests
├── simple-compiler: ~30 tests
├── simple-common:   ~6 tests
└── Other:          Various
```

## Next Steps for Native Codegen

1. **HIR Lowering**: Implement `lower.rs` to transform AST → HIR
2. **MIR Transform**: Implement HIR → MIR with basic blocks
3. **Cranelift Integration**: Wire MIR → Cranelift IR
4. **Testing**: Add native codegen tests alongside interpreter tests
