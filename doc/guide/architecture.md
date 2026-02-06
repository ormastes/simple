# Simple Language Architecture

## Overview

Simple is a self-hosting language where the compiler, standard library, and all tools are written in Simple itself. This guide explains the two-layer architecture that makes this possible.

---

## Two-Layer Architecture

Simple uses a two-layer design that separates runtime execution from language implementation:

```
┌─────────────────────────────────────────────────────────┐
│  Layer 2: Simple Compiler & Tools (100% Simple)        │
│  ├─ Compiler (src/compiler/)                           │
│  ├─ Standard Library (src/std/)                        │
│  ├─ Build System (src/app/build/)                      │
│  ├─ MCP Server (src/app/mcp/)                          │
│  ├─ LSP Server (src/app/lsp/)                          │
│  └─ All Development Tools                              │
└─────────────────────────────────────────────────────────┘
                          ↓
┌─────────────────────────────────────────────────────────┐
│  Layer 1: Bootstrap Runtime (Pre-Compiled Binary)      │
│  ├─ LLVM/Cranelift Code Generation                     │
│  ├─ Garbage Collector                                  │
│  ├─ FFI Bridge (System Libraries)                      │
│  ├─ Async I/O Runtime                                  │
│  └─ Simple Bytecode Executor                           │
└─────────────────────────────────────────────────────────┘
```

---

## Layer 1: Bootstrap Runtime (Pre-Compiled)

### Purpose
Provides the low-level execution environment for running Simple code.

### Components

**1. Code Generation**
- **Backends**: LLVM and Cranelift for native code generation
- **Optimization**: LLVM optimization passes for production builds
- **Target Support**: x86_64, ARM64, RISC-V (bare-metal capable)

**2. Memory Management**
- **Garbage Collector**: Generational GC with incremental collection
- **Allocator**: Custom allocator optimized for Simple's memory model
- **Reference Counting**: Optional RC for deterministic cleanup

**3. FFI Bridge**
- **System Calls**: File I/O, process management, networking
- **C Interop**: Call C libraries from Simple code
- **Platform Abstraction**: Unified API across Linux/macOS/Windows

**4. Async Runtime**
- **Green Threads**: Lightweight cooperative threads
- **I/O Reactor**: Epoll/kqueue/IOCP for async I/O
- **Task Scheduler**: Work-stealing scheduler for parallelism

### Size and Performance

| Build Type | Size | Use Case |
|------------|------|----------|
| Debug | 423 MB | Development (fast builds, debuggable) |
| Release | 40 MB | Standard optimized build |
| Bootstrap | 10 MB | Minimal size (distribution) |
| UPX Compressed | 4.5 MB | Maximum compression |

**Performance:**
- Native code generation via LLVM/Cranelift
- Zero-cost abstractions
- Inline caching for dynamic dispatch
- SIMD vectorization where applicable

### Source Code Location

- **Repository**: `rust/` directory (100% Rust)
- **Distribution**: Not included - users get pre-compiled binary
- **Modification**: Only needed for runtime developers

**Why Rust?**
- Memory safety for GC and FFI
- LLVM integration for code generation
- Cross-platform system library access
- High performance (comparable to C/C++)

---

## Layer 2: Simple Compiler & Tools (100% Simple)

### Purpose
All user-visible functionality implemented in Simple source code that users can read, modify, and extend.

### Components

**1. Compiler (src/compiler/)**

```
Lexer (lexer.spl)
    ↓
Parser (parser.spl)
    ↓
AST (ast.spl)
    ↓
HIR - High-Level IR (hir_definitions.spl)
    ↓
Type Inference (inference/*)
    ↓
MIR - Mid-Level IR (mir/*)
    ↓
Codegen (backend/codegen.spl)
    ↓
Native Code (via Layer 1)
```

**Key features:**
- 450,000+ lines of Simple code
- Complete type system implementation
- Pattern matching exhaustiveness checking
- Borrow checker (reference capabilities)
- Optimization passes

**2. Standard Library (src/std/)**

```
src/std/
├── collections/        # List, Dict, Set, Tree
├── io/                 # File, network, process
├── async/              # Async/await runtime
├── text/               # String manipulation
├── math/               # Math functions
├── testing/            # SSpec BDD framework
└── tooling/            # Coverage, profiling
```

**3. Build System (src/app/build/)**

Self-hosting build system with 8 phases:

| Phase | Command | Lines | Tests |
|-------|---------|-------|-------|
| Foundation | `build` | 500 | 30 |
| Testing | `test` | 550 | 45 |
| Coverage | `coverage` | 480 | 35 |
| Quality | `lint`, `fmt`, `check` | 620 | 50 |
| Bootstrap | `bootstrap` | 430 | 30 |
| Package | `package` | 520 | 40 |
| Migration | (internal) | 380 | 25 |
| Advanced | `watch`, `metrics` | 460 | 35 |

**4. Development Tools**

| Tool | Source | Lines | Description |
|------|--------|-------|-------------|
| MCP Server | `src/app/mcp/` | 2,500 | Model Context Protocol |
| LSP Server | `src/app/lsp/` | 3,200 | Language Server Protocol |
| DAP Server | `src/app/dap/` | 1,800 | Debug Adapter Protocol |
| Formatter | `src/app/fmt/` | 1,400 | Code formatting |
| Linter | `src/app/lint/` | 1,600 | Linting rules |

---

## Distribution Philosophy

### What Users Get

**In the distribution package:**
- ✅ Pre-compiled runtime binary (10 MB)
- ✅ Complete Simple compiler source (src/compiler/)
- ✅ Standard library source (src/std/)
- ✅ Build system source (src/app/build/)
- ✅ All tools source (src/app/)
- ✅ Examples and documentation

**NOT included:**
- ❌ Rust source code (rust/ directory)
- ❌ Build artifacts
- ❌ Test files (unless requested)

### Why This Design?

**Think of it like:**

| Simple | Similar To |
|--------|------------|
| Runtime | JVM / Python Interpreter |
| Simple Compiler | Java Compiler / Python Libraries |
| Distribution | JDK / Python Distribution |

**Key difference:** Unlike JVM/Python, you can modify the Simple compiler itself because it's written in Simple!

### User Experience

**For end users:**
```bash
# Download and run - no build needed
simple my_app.spl
```

**For library developers:**
```bash
# Modify compiler behavior
vim src/compiler/parser.spl
simple build bootstrap-rebuild
```

**For runtime developers:**
```bash
# Modify runtime (requires Rust)
cd rust/
cargo build --profile bootstrap
```

---

## Self-Hosting Process

### Three-Stage Bootstrap

```
Stage 1: Host Compiler (Previous Release)
    ↓ Compiles
Stage 2: Compiler v0.5.0 (Simple Source)
    ↓ Compiles
Stage 3: Verify (Recompile Stage 2)
```

**Verification:**
- Stage 2 and Stage 3 must produce identical binaries
- Proves the compiler can compile itself correctly

### Bootstrap Command

```bash
simple build bootstrap
# 1. Uses previous release runtime to compile current compiler
# 2. Uses newly compiled compiler to rebuild itself
# 3. Verifies binary checksums match
```

---

## Performance Characteristics

### Compilation Speed

| Component | Time | Optimizations |
|-----------|------|---------------|
| Lexer | ~0.5ms/1000 lines | Token streaming |
| Parser | ~1.5ms/1000 lines | Pratt parser |
| HIR Lowering | ~0.8ms/1000 lines | AST rewriting |
| Type Inference | ~2ms/1000 lines | Unification cache |
| MIR Generation | ~1ms/1000 lines | SSA construction |
| Codegen | ~5ms/1000 lines | LLVM backend |

**Total:** ~11ms per 1000 lines (debug mode)

### Runtime Performance

| Feature | Overhead | Notes |
|---------|----------|-------|
| Function Calls | 0% | Inlined by LLVM |
| Method Dispatch | 0-5% | Inline caching |
| Pattern Matching | 0% | Decision tree |
| Generics | 0% | Monomorphization |
| Closures | 0-2% | Lambda lifting |
| GC Allocation | 5-10% | Generational GC |

**Compared to native C/Rust:** 0.9-1.1x (within 10%)

---

## Extending Simple

### Adding Language Features

**1. Modify the Compiler (Simple)**

```simple
# src/compiler/parser.spl
fn parse_custom_syntax():
    # Add new syntax parsing
    match token:
        case KwCustom:
            parse_custom_block()
```

**2. Add HIR Representation**

```simple
# src/compiler/hir_definitions.spl
enum HirExpr:
    # ... existing variants
    CustomExpr(content: text, span: Span)
```

**3. Lower to MIR**

```simple
# src/compiler/hir_lowering/expr.spl
fn lower_expr(expr: HirExpr) -> MirInst:
    match expr:
        case CustomExpr(content, span):
            lower_custom(content, span)
```

**4. Test and Rebuild**

```bash
simple test src/compiler/parser_spec.spl
simple build bootstrap-rebuild
```

### Adding Standard Library Features

```simple
# src/std/my_module.spl
export fn my_function(x: i64) -> i64:
    x * 2

# No rebuild needed - just use it!
import std.my_module
val result = my_module.my_function(21)
```

---

## Platform Support

### Tier 1 Platforms (Fully Supported)

| Platform | Architecture | Status |
|----------|--------------|--------|
| Linux | x86_64 | ✅ |
| Linux | ARM64 | ✅ |
| macOS | x86_64 | ✅ |
| macOS | ARM64 (M1+) | ✅ |
| Windows | x86_64 | ✅ |

### Tier 2 Platforms (Cross-Compiled)

| Platform | Architecture | Status |
|----------|--------------|--------|
| Windows | ARM64 | ✅ Cross-compile |
| FreeBSD | x86_64 | 🔄 Testing |

### Tier 3 Platforms (Bare-Metal)

| Architecture | Use Case | Status |
|--------------|----------|--------|
| x86 32-bit | Embedded systems | 🔄 In progress |
| ARM Cortex-M | Microcontrollers | 🔄 In progress |
| RISC-V 32/64 | IoT/embedded | 🔄 In progress |

---

## Comparison with Other Languages

### Self-Hosting Languages

| Language | Compiler In | Runtime In | Distribution |
|----------|-------------|------------|--------------|
| **Simple** | **Simple** | **Rust** | **Source + Binary** |
| Rust | Rust | Rust | Source + Binary |
| Go | Go | C/Asm | Source + Binary |
| OCaml | OCaml | C | Source + Binary |
| Python | C | C | Interpreter + Libraries |
| Java | Java | C/C++ | JVM + Class Files |

**Simple's advantage:** Easiest to modify compiler (pure Simple, no C/Rust knowledge needed for compiler work)

---

## FAQ

**Q: Why not write the runtime in Simple too?**

A: The runtime needs:
- Direct memory management (GC, allocator)
- Low-level system calls (OS integration)
- LLVM/Cranelift integration (code generation)

These require unsafe operations that are better handled in Rust. Writing them in Simple would mean implementing a Simple runtime in Simple, which is circular.

**Q: Can I modify the runtime?**

A: Yes, but you'll need Rust installed. The runtime source is in the `rust/` directory (only in the development repository, not in distributions). Most users never need to touch the runtime.

**Q: How do I know the runtime is safe?**

A: The runtime is open source (Apache 2.0 license) and auditable. It's built from the GitHub repository with reproducible builds. SHA256 checksums are provided for verification.

**Q: What if I want a different runtime (e.g., WASM)?**

A: The Simple compiler can target different backends:
- LLVM (native code)
- Cranelift (fast JIT)
- Interpreter (debugging)
- WASM (web - in progress)

The compiler (Layer 2) stays the same; only the runtime (Layer 1) changes.

**Q: Can Simple run on embedded systems?**

A: Yes! Simple supports bare-metal targets:
- ARM Cortex-M (microcontrollers)
- RISC-V (IoT devices)
- x86 (embedded x86)

See the bare-metal examples in `examples/baremetal/`.

---

## Resources

- [Getting Started Guide](getting_started.md)
- [Building from Source](../build/building_from_source.md)
- [Contributing to the Compiler](../../CONTRIBUTING.md)
- [Runtime Development Guide](../development/runtime_development.md)

---

## Summary

Simple achieves self-hosting through a clean two-layer architecture:

1. **Layer 1 (Runtime)**: Pre-compiled binary providing execution environment
2. **Layer 2 (Compiler)**: 100% Simple source code for all user-visible functionality

This design gives users:
- ✅ No build required (pre-compiled runtime)
- ✅ Full compiler source to read and modify
- ✅ Fast compilation and execution
- ✅ Cross-platform support

The runtime is a black box (like JVM), but unlike Java, the entire compiler is transparent Simple code that you can modify without needing Rust knowledge.
