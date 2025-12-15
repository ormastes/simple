# Simple Language Features - Index

This document provides an overview of Simple language features organized by category.

## Feature Documentation Structure

- **[Core Features](features/core.md)** - Features #1-131: Basic language features, types, memory management, concurrency, module system, SIMD/GPU
- **[Extended Features](features/extended.md)** - Features #200-220: String unit types, networking APIs, LLVM backend
- **[Testing Features](features/testing.md)** - Features #300-303: BDD spec framework, doctest, test CLI, JJ integration
- **[Advanced Features](features/advanced.md)** - Features #400-536: Contracts, capability-based imports, UI framework, web framework
- **[Codegen Status](codegen_status.md)** - MIR instruction coverage, runtime FFI functions, implementation status

## Quick Reference by Category

### Core Language (Importance: 5)
- Basic Types, Variables, Control Flow, Functions
- Structs, Classes, Enums, Pattern Matching
- Array/Dict Types, Tuple Types
- Module System, Package Manager

### Memory Management
- GC-Managed Memory (default T) ✅
- Unique Pointers (&T, RAII)
- Shared Pointers (*T, refcounting)
- Borrowing ✅

### Concurrency
- Actors ✅
- Async/Await, Futures
- Generators ✅
- Isolated Threads, Channels

### Advanced Type System
- Type Inference (HM) 🔄
- Generics ✅
- Traits, Impl Blocks
- Union Types, Result/Option Types

### Metaprogramming
- Macros ✅
- Decorators, Attributes
- Derive Macros
- Context Blocks

### Unit Types & Semantic Typing
- Physical Units (length, time, velocity)
- Network Types (IpAddr, Port, Url)
- File System Types (FilePath)
- String Unit Suffixes

### Performance
- SIMD Vector Types
- GPU Compute Kernels
- Parallel Iterators
- LLVM Backend ✅

### Testing & Verification
- BDD Spec Framework ✅
- Doctest ✅
- Property-Based Testing
- Contract Blocks

### Developer Experience
- CLI/REPL ✅
- Watch Mode ✅
- Package Manager ✅
- Diagnostic Tools

### Web Development (Planned)
- UI Framework (.sui files)
- Web Framework (controllers, views)
- WASM Client Build
- SSR + Hydration

## Status Legend
- ✅ **COMPLETE** - Fully implemented
- 🔄 **IN PROGRESS** - Partially implemented
- 📋 **PLANNED** - Designed, not yet implemented
- 🔮 **FUTURE** - Long-term goal

## Implementation Priorities

### Phase 1: Core Language (Current)
Focus on features with **Importance: 5** and **Difficulty: 1-3**

### Phase 2: Type System & Safety
Type inference, borrowing, trait system

### Phase 3: Performance
SIMD, GPU, parallel execution

### Phase 4: Developer Tools
Enhanced testing, diagnostics, tooling

### Phase 5: Web Platform
UI/web frameworks, WASM support

## Dependency Guidelines

See [Architecture Documentation](architecture.md) for module dependency rules.

Key principles:
- **common**: shared contracts (ABI, GC handles, effect flags)
- **parser**: implements syntax from language spec
- **compiler**: depends on parser+common+runtime
- **runtime**: implements ABIs declared in common
- **driver**: orchestrates compile/load/run/watch

## Contributing

When implementing features:
1. Check the feature difficulty rating
2. Review architecture impact
3. Follow dependency guidelines
4. Add tests at appropriate levels (unit/integration/system)
5. Update status documentation

See [Development Guide](CLAUDE.md) for detailed development workflow.
