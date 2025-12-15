# Simple Language Features

**Note:** This file has been reorganized into focused documents for better maintainability.

## Main Documentation

📋 **[Feature Index](feature_index.md)** - Complete feature catalog with status, difficulty, and architecture impact

## Feature Categories

### Core Language Features (#1-131)
See full details in the main feature index. Key areas:
- **Basic Types** (i8-i64, u8-u64, f32-f64, bool, str, nil)
- **Variables, Functions, Control Flow**
- **Structs, Classes, Enums, Pattern Matching**
- **Memory Management** (GC ✅, Unique Pointers, Shared Pointers, Borrowing ✅)
- **Concurrency** (Actors ✅, Async ✅, Generators ✅)
- **Module System** (Parsing ✅, Resolution 🔄)
- **Package Manager** (UV-style ✅)
- **SIMD/GPU Support**

### Extended Features (#200-220)
- **Unit Types** (network, file system, string suffixes)
- **Networking** (TCP, UDP, HTTP, FTP)
- **LLVM Backend** ✅

### Testing Features (#300-303)
- **BDD Spec Framework** ✅ (Sprint 1 complete)
- **Doctest** ✅ (Sprint 2 complete)
- **Test CLI Integration** 📋 (planned)
- **JJ Version Control** 67% (8/12 tasks)

### Advanced Features (#400-536)
- **Contract Blocks** 📋 (requires/ensures/invariant)
- **Capability-Based Imports** 📋 (effect tracking)
- **UI Framework** 📋 (.sui files, GUI/TUI renderers)
- **Web Framework** 📋 (controllers, views, SSR)

## Implementation Status Overview

| Component | Status | Notes |
|-----------|--------|-------|
| **Lexer** | ✅ Complete | Indentation-based, all tokens |
| **Parser** | ✅ Complete | Modular (expressions/statements/types) |
| **AST** | ✅ Complete | Full node coverage |
| **HIR** | ✅ Complete | Type-checked IR |
| **MIR** | ✅ Complete | 50+ instructions, generator lowering |
| **Codegen** | 🔄 Hybrid | Cranelift + LLVM ✅, Interpreter fallback |
| **RuntimeValue** | ✅ Complete | 9 modules, 50+ FFI functions |
| **GC** | ✅ Complete | Abfall-backed with logging |
| **Actors/Async** | ✅ Complete | Runtime scheduler, effects |
| **Module System** | 🔄 Parsing | Resolution infrastructure ready |
| **Package Manager** | ✅ Complete | UV-style with lock files |
| **Testing** | 🔄 75% | BDD ✅, Doctest ✅, CLI integration pending |

## Quick Links

- **[Codegen Status](codegen_status.md)** - MIR instruction coverage, runtime FFI
- **[Architecture](architecture.md)** - Design principles, dependency rules
- **[Development Guide](CLAUDE.md)** - How to work on the compiler
- **[Test Documentation](test.md)** - Test strategy and coverage
- **[Language Spec](spec/language.md)** - Complete language specification

## Status Legend
- ✅ **COMPLETE** - Fully implemented and tested
- 🔄 **IN PROGRESS** - Partially implemented
- 📋 **PLANNED** - Designed, not yet started
- 🔮 **FUTURE** - Long-term goal

## Recent Completions

### December 2025
- ✅ LLVM Backend (32-bit + 64-bit, 43 tests)
- ✅ Generator State Machine Codegen
- ✅ Capture Buffer & VReg Remapping
- ✅ Dependency Tracker (module resolution, visibility, circular detection)
- ✅ BDD Spec Framework Sprint 1
- ✅ Doctest Sprint 2
- ✅ JJ Integration (8/12 tasks)

## Next Priorities

1. **Symbol Resolution** - Cross-module symbol lookup
2. **Test CLI Integration** - Unified `simple test` command
3. **Type Inference** - Complete HM implementation
4. **Codegen Expansion** - More MIR instruction coverage

See [feature_index.md](feature_index.md) for the complete feature catalog with detailed breakdowns, difficulty ratings, and implementation status.
