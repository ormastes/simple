---
name: Design Patterns Reference
description: Type system design, memory model, module system, MDSOC, pattern decisions for Simple
type: reference
---

## Design Principles
- Minimum complexity for current task, no hypothetical requirements
- Explicit over implicit, composition over inheritance
- Consistent naming, predictable behavior, clear errors, minimal API surface

## Pattern Decisions
| When | Use |
|------|-----|
| Sum types / variants | `enum Result<T,E>: Ok(T), Err(E)` |
| Plain data | `struct Point: x: Int, y: Int` |
| Data + behavior | `class Connection: socket: Socket; fn send()` |
| Abstraction | `trait Readable: fn read(n) -> Bytes` |

## Memory Model
- `T` shared (immutable), `mut T` exclusive (mutable), `iso T` isolated (transferable)
- Concurrency: `actor` (message passing), `lock_base` (traditional), `unsafe` (manual)

## Module System
- `__init__.spl` manifest with `requires [fs, net]`
- Effect decorators: `@pure`, `@io`, `@fs`, `@net`

## IR Levels
`Source → AST → HIR (type-checked) → MIR (50+ insns, effects) → Codegen (Cranelift/LLVM)`

## MDSOC (`src/compiler/85.mdsoc/`)
- 3-tier visibility: Public (via surface), Internal (same capsule), Private (same caret+folder)
- Caret (^): aspect root namespace. Virtual Capsule: composed module with explicit surface
- Modules: `types.spl`, `config.spl`, `layer_checker.spl`

## Adding New Types
1. Add variant in `src/compiler/30.types/`
2. Create module for complex types
3. Update type substitution + `contains_var()`
4. Export public API

## Doc Locations
- Design decisions: `doc/design/`
- Specs: `doc/spec/`
- Writing guides: `doc/guide/writing/design_writing.md`, `doc/guide/writing/architecture_writing.md`
