# Simple Language Code Statistics

**Generated:** 2026-03-14
**Version:** 0.6.1
**Status:** 100% Pure Simple Architecture

---

## Executive Summary

Simple is a **100% self-hosting Pure Simple** compiler and ecosystem:

- **Historical Rust codebase:** 467,846 lines (deleted 2026-02-05)
- **Current Simple codebase:** 1,245,587 lines (266% of original Rust)
- **Architecture:** 100% Pure Simple (zero Rust source)
- **Code expansion ratio:** 2.66x (Simple vs Rust)
- **Growth since v0.4.0:** +335,358 lines (+37%) in 5 weeks

---

## Current Simple Codebase (v0.6.1)

### Overall Statistics

| Metric | Value | Notes |
|--------|-------|-------|
| **Total Lines** | 1,245,587 | All .spl files |
| **Total Files** | 6,231 | .spl files only |
| **Production Code** | 791,038 lines | 3,893 files (63.5%) |
| **Test Code** | 399,549 lines | 2,181 files (32.1%) |
| **Examples** | 26,851 lines | 120 files (2.2%) |
| **Avg File Size** | 204 lines | |
| **Rust Source** | 0 | 100% Pure Simple |

### By Top-Level Directory

| Directory | Lines | Files | Purpose |
|-----------|-------|-------|---------|
| **src/** | 826,384 | 4,075 | Core implementation |
| **test/** | 364,203 | 1,999 | Test suites |
| **examples/** | 26,851 | 120 | Example programs |
| **doc/** | 27,711 | 29 | Documentation code |
| **bin/** | 239 | 4 | CLI entry points |

### Source Directory Breakdown (`src/`)

**Total: 826,384 lines across 4,075 files**

| Subdirectory | Lines | Files | Purpose |
|--------------|-------|-------|---------|
| **src/lib/** | 327,727 | 1,670 | Standard library |
| **src/compiler/** | 227,022 | 1,057 | Compiler infrastructure (lexer, parser, HIR, MIR, codegen) |
| **src/app/** | 91,521 | 577 | Applications (CLI, build, MCP, LSP, formatter, linter) |
| **src/i18n/** | 4,811 | 29 | Internationalization |

### Compiler Layers (`src/compiler/`)

**Total: 227,022 lines across 1,057 files**

| Layer | Lines | Files | Purpose |
|-------|-------|-------|---------|
| **70.backend/** | 53,087 | 205 | Backends (LLVM, C, Cranelift, WASM, CUDA, Vulkan) |
| **90.tools/** | 35,690 | 192 | API surface, coverage, symbol analyzer |
| **10.frontend/** | 35,004 | 101 | Lexer, parser, AST, treesitter |
| **80.driver/** | 19,792 | 91 | Driver, pipeline, build mode |
| **30.types/** | 18,970 | 56 | Type inference, type system |
| **35.semantics/** | 11,654 | 47 | Semantic analysis, lint, resolve |
| **60.mir_opt/** | 7,213 | 23 | MIR optimization passes |
| **99.loader/** | 6,827 | 23 | Module resolver, loader |
| **40.mono/** | 6,417 | 22 | Monomorphization |
| **00.common/** | 5,876 | 37 | Error types, config, diagnostics |
| **85.mdsoc/** | 5,227 | 151 | Virtual capsules, AOP |
| **20.hir/** | 4,975 | 19 | HIR types, definitions, lowering |
| **50.mir/** | 4,667 | 17 | MIR types, lowering, serialization |
| **15.blocks/** | 4,447 | 26 | Block definition system |
| **55.borrow/** | 2,844 | 10 | Borrow checking, GC analysis |
| **25.traits/** | 1,947 | 9 | Trait def, impl, solver |
| **95.interp/** | 1,829 | 14 | Interpreter, MIR interpreter |

### Standard Library (`src/lib/`)

**Total: 327,727 lines across 1,670 files**

| Category | Lines | Files | Purpose |
|----------|-------|-------|---------|
| **common/** | 146,275 | 713 | Pure functions (text, math, json, crypto) |
| **nogc_sync_mut/** | 126,495 | 639 | Sync mutable (ffi, fs, net, http, spec) |
| **nogc_async_mut/** | 30,986 | 153 | Async mutable (actors, async, threads) |
| **nogc_async_mut_noalloc/** | 13,138 | 89 | Baremetal, execution, memory |
| **nogc_async_immut/** | 5,214 | 22 | Async immutable |
| **gc_async_mut/** | 4,985 | 23 | GC + async (gpu, cuda, torch, ML) |

### Test Statistics

| Metric | Value |
|--------|-------|
| **Total Test Files** | 2,181 |
| **Test Lines** | 399,549 |
| **Test Ratio** | 33.5% of total lines |

---

## Historical Rust Codebase (Pre-v0.4.0)

### Total Rust Code (as of 2026-02-03)

- **467,846 lines** across 16 crates
- **~2,000+ files** (.rs files)
- **48.1 GB total** (including artifacts and backups)

### Rust Crate Breakdown

| Crate | Lines | % of Total | Purpose |
|-------|-------|------------|---------|
| **compiler** | 187,317 | 40.0% | Self-hosting compiler (parser, HIR, MIR, codegen) |
| **runtime** | 90,171 | 19.3% | RuntimeValue, GC, FFI registry |
| **driver** | 36,882 | 7.9% | CLI driver and dispatcher |
| **parser** | 29,213 | 6.2% | Lexer and parser |
| **loader** | 11,156 | 2.4% | Module loading and resolution |
| **type** | 6,605 | 1.4% | Type system and inference |
| **common** | 5,325 | 1.1% | Common utilities |
| **gpu** | 4,425 | 0.9% | GPU acceleration |
| **sdn** | 3,779 | 0.8% | SDN parser |
| **simd** | 2,241 | 0.5% | SIMD operations |
| **dependency_tracker** | 2,161 | 0.5% | Dependency tracking |
| **wasm-runtime** | 1,803 | 0.4% | WASM support |
| **hir-core** | 1,390 | 0.3% | HIR core types |
| **native_loader** | 1,263 | 0.3% | Native symbol loading |
| **log** | 942 | 0.2% | Logging infrastructure |
| **lib** | 33 | 0.0% | Minimal utilities |
| **Build files** | ~82,000 | 17.5% | Cargo.toml, build scripts |

### Rust Deletion Strategy

| Category | Lines | % | Status |
|----------|-------|---|--------|
| **Legacy code** | 242,530 | 52% | ✅ Deleted (replaced by Simple) |
| **FFI wrappers** | 137,276 | 29% | ✅ Deleted (rewrote in Pure Simple) |
| **Keep/migrate** | 88,940 | 19% | ✅ Migrated to Simple or deleted |
| **TOTAL** | **468,746** | **100%** | ✅ All Rust deleted |

---

## Rust → Simple Transition

### Timeline

| Date | Event | Rust Lines | Simple Lines |
|------|-------|------------|--------------|
| 2026-01-20 | Migration begins | 467,846 | ~200,000 |
| 2026-02-03 | Rust removal planning | 467,846 | ~400,000 |
| 2026-02-04 | Pure Simple Phase 1-3 | 467,846 | ~600,000 |
| 2026-02-05 | **Phase 4 Complete** | **0** ✅ | **910,229** ✅ |

### Code Expansion Analysis

| Language | Lines | Files | Ratio |
|----------|-------|-------|-------|
| **Rust (historical)** | 467,846 | ~2,000 | 1.00x |
| **Simple (current)** | 910,229 | 3,879 | **1.95x** |

**Expansion Breakdown:**
- Production code: 508,302 lines (1.09x of Rust)
- Test code: 401,927 lines (0.86x of Rust)

**Why the expansion?**
1. **More explicit syntax** - Simple is higher-level and more expressive
2. **Comprehensive tests** - 44.2% test coverage (401K test lines)
3. **Self-hosting build system** - Written in Simple (4,440 lines)
4. **Rich standard library** - 30,581 lines of stdlib
5. **Multiple implementations** - Release artifacts, examples, i18n

### Component Migration

| Component | Rust Lines | Simple Lines | Change | Status |
|-----------|------------|--------------|--------|--------|
| **Compiler** | 187,317 | 83,250 | -56% | ✅ Complete |
| **Runtime** | 90,171 | (Pure Simple) | N/A | ✅ Replaced |
| **Driver/CLI** | 36,882 | 82,292 (app/) | +123% | ✅ Enhanced |
| **Parser** | 29,213 | (in compiler) | -100% | ✅ Integrated |
| **Standard Library** | ~10,000 | 30,581 | +206% | ✅ Expanded |
| **Build System** | (Cargo) | 93,621 | N/A | ✅ Self-hosting |
| **Tests** | ~50,000 | 401,927 | +704% | ✅ Comprehensive |

---

## Code Quality Metrics

### File Size Distribution

| Range | Count |
|-------|------:|
| > 2000 lines | 2 |
| 1000-1499 | 13 |
| 800-999 | 20 |
| 500-799 | 447 |
| 200-499 | 1,936 |
| < 200 lines | 3,678 |

### Code Organization

| Metric | Value |
|--------|-------|
| **Average file size** | 204 lines |
| **Largest file** | 2,415 lines (`src/app/cli/query_rich.spl`) |
| **Total .spl files** | 6,231 |
| **Documentation files** | 4,282 .md files |
| **SDN data files** | 336 .sdn files |
| **Module organization** | Hierarchical by feature, numbered compiler layers |

---

## Language Feature Usage

### Simple Language Features

| Feature | Usage Count | Examples |
|---------|-------------|----------|
| **Classes** | 500+ | `StringInterner`, `SdnDatabase`, `Compiler` |
| **Functions** | 5,000+ | Throughout codebase |
| **Structs** | 300+ | `Point`, `Token`, `ASTNode` |
| **Enums** | 200+ | `TokenType`, `OpCode`, `ErrorKind` |
| **Pattern matching** | 2,000+ | `match` statements everywhere |
| **Generics** | 150+ | `Option<T>`, `Result<T, E>`, `List<T>` |
| **Lambdas** | 500+ | `.map(\x: x * 2)` |
| **Pipeline operators** | 100+ | `|>`, `>>`, `~>` (DL) |

### Syntax Patterns (Recent Refactoring)

| Old Pattern | New Pattern | Occurrences Refactored |
|-------------|-------------|------------------------|
| `opt.is_some()` | `opt.?` | 200+ |
| `opt.is_none()` | `not opt.?` | 150+ |
| `if let` | `if val` | 300+ |
| `Option[T]` | `Option<T>` | 500+ |

---

## File Type Distribution

### By Extension

| Extension | Files | Purpose |
|-----------|-------|---------|
| **.spl** | 6,231 | Simple source code (1,245,587 lines) |
| **.sdn** | 336 | Data files (SDN format) |
| **.md** | 4,282 | Documentation |
| **.shs** | 15 | Shell scripts (Simple) |
| **.c/.h** | 5,276 | Generated C bootstrap |
| **.rs** | 1,908 | Legacy/generated artifacts |

### By Purpose

| Type | Files | Lines | % |
|------|-------|-------|---|
| **Production** | 3,893 | 791,038 | 63.5% |
| **Tests** | 2,181 | 399,549 | 32.1% |
| **Examples** | 120 | 26,851 | 2.2% |
| **Other** | 37 | 28,149 | 2.3% |

---

## Growth Trends

### Version History

| Version | Date | Simple Lines | Rust Lines | Architecture |
|---------|------|--------------|------------|--------------|
| **0.1.x** | 2025-Q4 | ~50,000 | 400,000 | Rust-based |
| **0.2.x** | 2025-Q4 | ~150,000 | 450,000 | Hybrid |
| **0.3.x** | 2026-Q1 | ~400,000 | 467,846 | Self-hosting |
| **0.4.0** | 2026-02-05 | 910,229 | 0 | 100% Pure Simple |
| **0.6.1** | 2026-03-14 | **1,245,587** | **0** ✅ | **100% Pure Simple** |

### Line Count Growth

```
Rust decline:    467K → 0        (-467K, -100%)
Simple growth:   50K → 1,246K    (+1,196K, +2392%)
Total codebase:  517K → 1,246K   (+729K, +141%)
```

### Monthly Growth (2026)

| Month | Simple Lines Added | Notable Changes |
|-------|-------------------|-----------------|
| **January** | +300,000 | Self-hosting build system, database library |
| **February** | +510,000 | Pure Simple transition, Rust deletion |
| **March** | +335,000 | Stdlib expansion, compiler layers, examples |

---

## Architecture Breakdown

### Current Architecture (v0.6.1)

```
100% Pure Simple (1,246K lines)
├── Compiler (227K lines, 17 layers)
│   ├── 00.common → 10.frontend → 15.blocks → 20.hir
│   ├── 25.traits → 30.types → 35.semantics → 40.mono
│   ├── 50.mir → 55.borrow → 60.mir_opt
│   ├── 70.backend (LLVM, C, Cranelift, WASM, CUDA, Vulkan)
│   ├── 80.driver → 85.mdsoc → 90.tools
│   └── 95.interp → 99.loader
│
├── Standard Library (328K lines)
│   ├── common/ (146K) - Pure functions
│   ├── nogc_sync_mut/ (126K) - Sync mutable
│   ├── nogc_async_mut/ (31K) - Async mutable
│   ├── nogc_async_mut_noalloc/ (13K) - Baremetal
│   ├── nogc_async_immut/ (5K) - Async immutable
│   └── gc_async_mut/ (5K) - GC + async (GPU, ML)
│
├── Applications (92K lines)
│   ├── CLI dispatcher
│   ├── Build system (self-hosting)
│   ├── MCP server
│   ├── LSP server
│   ├── Formatter, linter
│   └── Package manager
│
├── Tests (364K lines)
│   ├── Unit, integration, system, feature tests
│   └── 2,181 test files
│
└── Examples (27K lines)
    ├── Deep learning, CUDA, GPU
    └── TRACE32 tools, CMM LSP
```

---

## Comparison: Rust vs Simple

### Language Characteristics

| Metric | Rust | Simple | Difference |
|--------|------|--------|------------|
| **Average LOC per feature** | 100 | 195 | +95% |
| **Verbosity** | Low | Medium | Higher-level |
| **Explicit types** | Required | Inferred | Less boilerplate |
| **Memory management** | Manual (borrow checker) | GC/runtime | Simpler |
| **Error handling** | `Result<T, E>` | `Result<T, E>` + `?` | Similar |
| **Pattern matching** | Required | Required | Similar |

### Code Density

| Category | Rust (lines/file) | Simple (lines/file) | Ratio |
|----------|-------------------|---------------------|-------|
| **Implementation** | 234 | 249 | 1.06x |
| **Tests** | 250 | 219 | 0.88x |
| **Average** | 234 | 235 | 1.00x |

**Conclusion:** File sizes are comparable, but total codebase is larger due to:
- More comprehensive test suite
- Expanded standard library
- Self-hosting build system
- Release artifacts and examples

---

## Performance Metrics

### Binary Sizes

| Profile | Size | Compression | Use Case |
|---------|------|-------------|----------|
| **Debug** | 423 MB | N/A | Development |
| **Release** | 40 MB | N/A | Standard |
| **Bootstrap** | 9.3 MB | N/A | Minimal (76.8% reduction) |
| **Bootstrap + UPX** | ~4.5 MB | LZMA | Maximum (88.8% reduction) |

### Build Times (estimated)

| Target | Time | Notes |
|--------|------|-------|
| **Debug build** | ~2 min | Fast iteration |
| **Release build** | ~5 min | Optimized |
| **Bootstrap** | ~10 min | 3-stage pipeline |
| **Full test suite** | ~15 min | 631+ tests |

---

## Future Projections (v0.5.0)

### Planned Additions

| Feature | Estimated Lines | Status |
|---------|----------------|--------|
| Grammar refactoring | +5,000 | Planned |
| DL module fixes | +2,000 | In progress |
| Enhanced LSP | +10,000 | Planned |
| TUI framework | +15,000 | Planned |
| Package registry | +8,000 | Planned |
| **Total Growth** | **+40,000** | |

### Projected Statistics (v0.5.0)

| Metric | v0.4.0 | v0.5.0 (est.) | Change |
|--------|--------|---------------|--------|
| **Total lines** | 910,229 | ~950,000 | +4% |
| **Production** | 508,302 | ~550,000 | +8% |
| **Tests** | 401,927 | ~400,000 | 0% |
| **Features** | 631+ | ~750 | +19% |

---

## Key Achievements

### v0.6.1 Milestones (2026-03-14)

- ✅ **1.25M lines of Simple code** - 2.66x original Rust codebase
- ✅ **6,231 source files** - Well-organized, modular codebase
- ✅ **17-layer compiler** - Numbered layers (00-99) for clear dependency order
- ✅ **328K stdlib** - Comprehensive standard library across 6 categories
- ✅ **92K app code** - CLI, build system, MCP, LSP, formatter, linter
- ✅ **27K examples** - Deep learning, CUDA, TRACE32, GPU

### Growth Milestones

- **v0.4.0 → v0.6.1:** +335K lines (+37%) in 5 weeks
- **Rust → Simple:** 467K Rust deleted, replaced by 1.25M Simple
- **Compiler growth:** 83K → 227K lines (+173%)
- **Stdlib growth:** 31K → 328K lines (+958%)
- **Average file size:** 204 lines (well within maintainability target)

---

## Summary

Simple v0.6.1 is a **1.25 million line self-hosting compiler ecosystem**:

- **From:** 467K lines of Rust (16 crates)
- **To:** 1,245,587 lines of Simple (100% self-hosting)
- **Change:** +778K lines (+166%), 0 Rust source files remaining
- **Architecture:** 17-layer compiler, 6-category stdlib, 50+ app modules

The project demonstrates that a **self-hosting compiler** can be written entirely in its own language, with comprehensive testing (400K test lines), robust tooling, and production-ready infrastructure — built with LLM-assisted development.

---

**Last Updated:** 2026-03-14
**Generated by:** Simple Code Statistics Tool
