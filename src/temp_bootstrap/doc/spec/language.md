# Simple Language Specification

This is the main specification index for the Simple programming language. The specification is organized into focused documents covering different aspects of the language.

## Specification Documents

### Core Language

| Document | Description |
|----------|-------------|
| [Syntax](syntax.md) | Execution modes, lexical structure, literals, operators, parsing rules |
| [Types](types.md) | Type system, mutability rules, unit types, type inference |
| [Units](units.md) | Unit types, semantic typing, primitive restrictions |
| [Data Structures](data_structures.md) | Structs, classes, enums, unions, strong enums |
| [Functions](functions.md) | Functions, lambdas, pattern matching, constructor polymorphism |
| [Traits](traits.md) | Traits, implementations, trait bounds, polymorphism |
| [Memory](memory.md) | Memory management, ownership, pointer types, borrowing |

### Advanced Features

| Document | Description |
|----------|-------------|
| [Concurrency](concurrency.md) | Actors, async/await, isolated threads, futures |
| [Metaprogramming](metaprogramming.md) | Macros, DSL features, decorators, comprehensions |
| [Standard Library](stdlib.md) | Stdlib overview, variants, modules, configuration |
| [GPU & SIMD](gpu_simd.md) | GPU programming, SIMD types, parallel compute |

### Parser & Lexer

| Document | Description |
|----------|-------------|
| [Lexer & Parser](lexer_parser.md) | Token types, grammar rules, AST structure |

### Module System

| Document | Description |
|----------|-------------|
| [Import/Export](../import_export_and__init__.md) | Module system, imports, exports, visibility |

---

## Quick Reference

### Execution Modes

Simple supports two execution modes:

- **Compiler Mode** - Requires explicit type annotations, compiles to native code via Cranelift
- **Interpreter Mode** - Type annotations optional, supports dynamic typing

### Key Language Features

- **Indentation-based syntax** (Python-like)
- **Strong static typing** with type inference
- **Semantic typing** - unit types instead of bare primitives
- **No implicit nil** - must use `Option[T]` (compile error otherwise)
- **Immutability by default** for structs
- **Actor-based concurrency** (Erlang-inspired)
- **Pattern matching** with guards and destructuring
- **First-class functions** and closures
- **Traits** for polymorphism
- **Macros** for metaprogramming
- **Multiple pointer types** (GC, unique, shared, weak, handle)

### Type Overview

| Category | Types |
|----------|-------|
| Primitives | `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, `u64`, `f32`, `f64`, `bool`, `str` |
| Compound | `(T1, T2)` tuples, `[T]` arrays, `{K: V}` dicts |
| User-defined | `struct`, `class`, `enum`, `trait` |
| Pointers | `T` (GC), `&T` (unique), `*T` (shared), `-T` (weak), `+T` (handle) |

### Mutability Summary

| Declaration | Default | Override |
|-------------|---------|----------|
| `struct` | Immutable | `mut struct` |
| `class` | Mutable | `immut class` |
| Variables | Mutable | `const` |

### Concurrency Models

| Model | Use Case |
|-------|----------|
| Standard Actors | General message-passing concurrency |
| Stackless Actors | High-performance, guaranteed non-blocking |
| Isolated Threads | CPU-bound parallelism |
| Async/Await | Asynchronous I/O |

---

## Document Organization

The specification documents are organized as follows:

```
doc/spec/
├── language.md           # This index file
├── syntax.md             # Lexical structure and syntax
├── types.md              # Type system
├── units.md              # Unit types and semantic typing
├── data_structures.md    # Structs, classes, enums
├── functions.md          # Functions and pattern matching
├── traits.md             # Traits and implementations
├── memory.md             # Memory and ownership
├── concurrency.md        # Concurrency primitives
├── metaprogramming.md    # Macros and DSL features
├── stdlib.md             # Standard library
├── gpu_simd.md           # GPU and SIMD
└── lexer_parser.md       # Parser specification
```

## Project Directory Structure

```
simple/
├── lib/                  # Simple standard library (written in Simple)
│   └── std/              # stdlib root with __init__.spl
├── native_lib/           # Native system interface (written in Rust)
│   ├── core/             # Memory, GC, math intrinsics
│   ├── io/               # Filesystem, networking, terminal
│   ├── sys/              # Args, env, process, time
│   └── sync/             # Mutexes, channels, atomics
└── src/                  # Compiler implementation (Rust)
```

See [Standard Library](stdlib.md) for detailed directory layout.

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 0.1 | - | Initial specification |
