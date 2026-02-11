# compiler vs compiler_core

**Architecture Decision:** These directories contain intentionally duplicated code.

## Why Duplication Exists

- **compiler/**: Full Simple implementation (~52K lines) using advanced language features
  - Generics (`Option<T>`, `Result<T, E>`)
  - Trait implementations (`impl Trait for Type`)
  - Closures and higher-order functions
  - Complex pattern matching
  - Multi-line boolean expressions

- **compiler_core/**: Desugared Core Simple version (~44K lines) for bootstrap compatibility
  - No generics (monomorphized to concrete types)
  - No trait implementations (module-level functions)
  - No closures (lambda-lifted to top-level)
  - Simplified patterns
  - Single-line boolean expressions

## Bootstrap Process

```
seed.cpp (C++ seed compiler)
  → compiles Core Simple (compiler_core/)
  → produces initial Simple compiler
  → compiles Full Simple (compiler/)
  → self-hosting complete
```

## DO NOT Merge

Attempting to merge these directories will break the bootstrap process.
The duplication is necessary until the desugaring pipeline is fully automated.

See DESUGARING_PLAN.md for transformation rules and details.

## Type Mappers

Both directories contain type mapper files for each backend:
- `llvm_type_mapper.spl`
- `cuda_type_mapper.spl`
- `wasm_type_mapper.spl`
- `cranelift_type_mapper.spl`
- `vulkan_type_mapper.spl`
- `interpreter_type_mapper.spl`

The Full Simple versions use trait implementations for polymorphism.
The Core Simple versions use module-level functions for the same purpose.

This architectural duplication is intentional and required for bootstrap.
