# Simple Language Implementation Status

## Overview

This directory tracks the implementation status of language features.

## Component Status

| Component | Status | Notes |
|-----------|--------|-------|
| **Lexer** | Complete | Tokens, INDENT/DEDENT, comments |
| **Parser** | Complete | Full AST generation |
| **Type Checker** | Partial | Basic HM inference scaffold |
| **HIR** | Stub | Structure exists, minimal lowering |
| **MIR** | Stub | Types defined, no transformation |
| **Cranelift Codegen** | Stub | Not generating real code |
| **Interpreter** | **Complete** | Tree-walking, all features |
| **SMF Loader** | Complete | Binary format loading |
| **Driver/CLI** | Complete | Run, watch modes |
| **Runtime/GC** | Complete | Abfall-backed wrapper |

## Execution Model

The Simple language currently uses a **tree-walking interpreter** for execution:

```
Source (.spl) → Lexer → Parser → AST → Type Check → Interpreter → Result
                                              ↓
                                    SMF (returns interpreter result)
```

The SMF binary currently just packages the interpreter's result as x86-64 `mov eax, <result>; ret`.

## Test Summary

```
Total tests: 425+ passing (19 failing in collections)
├── Parser tests: ~180
├── Interpreter tests: ~100
├── Type checker tests: ~22
├── Compiler tests: ~30
├── Common tests: ~6
└── Other: Various
```

Run tests:
```bash
cargo test --workspace
```

## Feature Status Summary

| Status | Count | Description |
|--------|-------|-------------|
| Interpreter Complete | 48 | Working via tree-walking interpreter |
| Native Codegen | 0 | HIR/MIR/Cranelift are stubs |
| Partial | 19 | Some tests failing (Result, decorators, with) |

## Features by Implementation Level

### Fully Working (Interpreter)

All 48 original features work through the interpreter:

| Category | Features |
|----------|----------|
| **Core** | Basic types, variables, operators, control flow, loops, functions |
| **Data Types** | Structs, classes, enums, tuples, arrays, dicts, unions |
| **Type System** | Type inference (HM scaffold), generics, traits, impl blocks |
| **Memory** | GC-managed, unique/shared/weak/handle pointers, borrowing |
| **Concurrency** | Actors, spawn/send/recv, async/await, futures, generators |
| **Syntax** | Comments, indentation blocks, lambdas, pattern matching |
| **Advanced** | Macros, context blocks, method missing, string interpolation |

### Partially Working (19 failing tests)

| Feature | Issue |
|---------|-------|
| Result type | `Ok`/`Err` not in scope |
| `?` operator | Depends on Result |
| Decorators | Some edge cases failing |
| `with` statement | Class enter/exit issues |
| `if let`/`while let` | Pattern binding issues |

### Not Yet Implemented (Features 49-98)

| # | Feature | Difficulty |
|---|---------|------------|
| 49-55 | CLI enhancements (SMF gen, REPL, -c) | 2-3 |
| 56-61 | Package manager | 2-4 |
| 62-70 | Python-style syntax (comprehensions, slicing, decorators) | 2-3 |
| 71-81 | Rust-style features (attributes, match guards, derive) | 2-3 |
| 82 | Auto-forwarding properties | 3 |
| 83-86 | Isolated threads, channels | 3-4 |
| 87-92 | Unit types, literal suffixes | 2-4 |
| 93-98 | Numeric literals, constructor polymorphism | 1-3 |

## Native Compilation Pipeline (TODO)

To achieve native compilation (not interpreter):

1. **HIR Lowering** - AST → typed HIR
2. **MIR Transformation** - HIR → simplified MIR
3. **Cranelift Codegen** - MIR → machine code

Current blockers:
- HIR/MIR types exist but no real transformation
- Cranelift module structure exists but not wired up
- SMF generation uses interpreter result, not codegen

## Concurrency Support (Interpreter)

| Feature | Status |
|---------|--------|
| `spawn` | Working |
| `send/recv` | Working (timeout-based) |
| `join` | Working |
| `reply` | Working |
| `async/await` | Working |
| `future` | Working |
| `generator` | Working |

## Pointer/Memory Support (Interpreter)

| Pointer Type | Syntax | Status |
|--------------|--------|--------|
| GC (default) | `T` | Working |
| Unique | `&T` | Working |
| Shared | `*T` | Working |
| Weak | `-T` | Working |
| Handle | `+T` | Working |
| Borrow | `&T` | Working |
| BorrowMut | `&mut T` | Working |

## Architecture

See `CLAUDE.md` and `doc/architecture/overview.md` for design principles.

## Individual Feature Status Files

Each `.md` file in this directory documents a specific feature's status:
- Implementation approach
- Test coverage
- Known issues
- Next steps
