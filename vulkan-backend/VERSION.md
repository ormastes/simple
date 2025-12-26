# Simple Language Version History

## Current Version: 0.1.0

## Versions

### 0.1.0 (2024-12)

Initial release with core language features and tooling.

#### Language Features
- Basic types: integers (i8-i64, u8-u64), floats (f32, f64), bool, str, nil
- Variables with `let`, `const`, and type inference
- Control flow: if/elif/else, for, while, loop, break, continue
- Functions with parameters and return types
- Structs (immutable by default) and classes (mutable by default)
- Enums with variants and pattern matching
- Arrays, dictionaries, and tuples
- Lambdas with `\x: expr` syntax
- String interpolation with `"Hello, {name}!"`
- Operators: arithmetic, comparison, logical, bitwise
- Indentation-based blocks (Python-like)
- Comments with `#`

#### Compiler & Runtime
- Tree-walking interpreter for compile-time evaluation
- SMF (Simple Module Format) binary generation
- x86-64 native code generation via Cranelift
- GC-managed memory with Abfall collector
- No-GC mode for manual memory management
- In-memory compilation and execution

#### CLI (`simple` command)
- Interactive REPL with history
- Run source files: `simple file.spl`
- Run compiled binaries: `simple file.smf`
- Run code strings: `simple -c "expr"`
- Compile command: `simple compile src.spl -o out.smf`
- Watch mode: `simple watch file.spl`
- GC options: `--gc-log`, `--gc=off`

#### Testing
- 1,200+ tests across unit, integration, and system levels
- Coverage tracking per test level
- Code duplication detection

---

## Planned Versions

### 0.2.0 (Planned)
- Generics and type parameters
- Traits (interfaces)
- Improved error messages
- Standard library basics

### 0.3.0 (Planned)
- Actors and message passing
- Async/await with futures
- Concurrency primitives

### 0.4.0 (Planned)
- Borrowing and lifetime analysis
- Unique and shared pointers
- Memory safety verification

### 1.0.0 (Planned)
- Stable language specification
- Complete standard library
- Production-ready tooling

---

## Version Numbering

Simple follows [Semantic Versioning](https://semver.org/):

- **MAJOR** (x.0.0): Breaking changes to language or APIs
- **MINOR** (0.x.0): New features, backward compatible
- **PATCH** (0.0.x): Bug fixes, backward compatible

Pre-1.0 versions may have breaking changes in minor releases.
