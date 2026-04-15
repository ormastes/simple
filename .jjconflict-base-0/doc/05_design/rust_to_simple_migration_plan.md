# Rust to Simple Migration Plan - Bottom-Up Analysis

**Document Version:** 1.0
**Date:** 2026-01-30
**Target Version:** 0.4.0

---

## Executive Summary

The Simple compiler consists of **25 Rust crates** organized in 6 dependency layers. Analysis shows:

- **10 crates MUST stay Rust** (FFI, unsafe, low-level)
- **12 crates HIGH port potential** (business logic, algorithms)
- **3 crates MEDIUM port potential** (mixed concerns)

**Target for v0.4.0:** Port 12 high-potential crates = 48% of crates, ~60-70% of lines (high-level code is verbose).

---

## Layer 0: Foundation (KEEP RUST)

### `hir-core` - Shared HIR Types
**Purpose:** Shared data structures for compiler and interpreter
**Key Types:** `LogLevel`, `PrimitiveKind`, `StructLayout`, `EnumLayout`, `TokenCategory`
**Dependencies:** Only `serde`
**Verdict:** ❌ **MUST STAY RUST** — Shared type definitions with serde integration

---

## Layer 1: Core Infrastructure

### `common` - Common Utilities (MIXED)
**Purpose:** Shared utilities, module loading abstractions, GC interfaces
**Key Modules:** `DynModule`, `DynLoader`, `ModuleCache`, `Target`, `Diagnostic`, `EasyFix`
**Dependencies:** `ahash`, `memmap2`, `serde`, `thiserror`
**Port Potential:** 🟡 **PARTIAL** — Abstractions yes, FFI/GC interfaces no

### `sdn` - SDN Parser (PORT TO SIMPLE) ⭐
**Purpose:** Parse `.sdn` config/data files (Simple Data Notation)
**Key Types:** `SdnValue`, `SdnDocument`, parser, lexer
**Dependencies:** `thiserror`, `indexmap`, `hir-core`
**Port Potential:** ✅ **HIGH** — Pure parsing logic, excellent first candidate
**Lines:** ~2,000
**Priority:** **Phase 1** (Quick Win)

### `type` - Type System Utilities (PORT TO SIMPLE)
**Purpose:** Type checking and inference helpers
**Dependencies:** `parser`
**Port Potential:** ✅ **MEDIUM-HIGH** — Type logic, depends on parser
**Priority:** **Phase 3**

---

## Layer 2: Parser & Core Services

### `parser` - Lexer and Parser (KEEP RUST)
**Purpose:** Tokenize and parse Simple source code into AST
**Key Modules:** `lexer`, `token`, `ast`, `parser_impl`, `interner`, `diagnostic`, `doc_gen`
**Dependencies:** `lasso` (string interning), `typed-arena`, `smallvec`, `memmap2`
**Port Potential:** 🟡 **LOW** — Performance-critical, uses arena allocators
**Lines:** ~15,000+
**Verdict:** ❌ **KEEP RUST** — Or accept 3-5x performance penalty

### `dependency_tracker` - Module Resolution (PORT TO SIMPLE) ⭐
**Purpose:** Resolve module paths, track dependencies, enforce visibility
**Key Modules:** `resolution`, `visibility`, `macro_import`, `graph`
**Dependencies:** `common`, `parser`, `thiserror`
**Port Potential:** ✅ **HIGH** — Graph algorithms, pure logic
**Lines:** ~1,500
**Priority:** **Phase 3**

### `diagnostics` - Error Reporting (PORT TO SIMPLE) ⭐
**Purpose:** Error/warning reporting with i18n support
**Key Types:** `Diagnostic`, `Severity`, `Span`, `Label`
**Dependencies:** `simple_i18n`, `hir-core`, `serde`
**Port Potential:** ✅ **HIGH** — Business logic for formatting
**Lines:** ~1,000
**Priority:** **Phase 1** (Quick Win)

---

## Layer 3: Loaders & Hardware (ALL KEEP RUST)

### `loader` - SMF Module Loader
**Purpose:** Load compiled `.smf` binaries
**Verdict:** ❌ **MUST STAY RUST** — Binary format, mmap, platform-specific

### `native_loader` - Dynamic Library Loader
**Purpose:** Load `.so`/`.dll`/`.dylib` via FFI
**Verdict:** ❌ **MUST STAY RUST** — Direct FFI and dynamic linking

### `simd` - SIMD Operations
**Purpose:** SIMD vector types
**Verdict:** ❌ **MUST STAY RUST** — Hardware SIMD intrinsics

### `gpu` - GPU Compute
**Purpose:** CUDA/ROCm GPU backends
**Verdict:** ❌ **MUST STAY RUST** — Hardware FFI

### `embedded` - Bare-Metal Runtime
**Purpose:** `no_std` runtime for ARM Cortex-M, RISC-V
**Verdict:** ❌ **MUST STAY RUST** — Bare-metal startup, interrupt handling

---

## Layer 4: Runtime & Compilation

### `runtime` - Core Runtime (KEEP RUST)
**Purpose:** GC, async executor, value representation, FFI functions
**Key Modules:** `value`, `gc`, `executor`, `async_runtime`, `memory`, `concurrency`
**Crate Type:** `["rlib", "staticlib", "cdylib"]`
**Dependencies:** 20+ crates (abfall, tch, rayon, vulkan, etc.)
**Verdict:** ❌ **MUST STAY RUST** — Memory management, unsafe FFI, platform concurrency
**Lines:** ~30,000+

### `compiler` - Main Compiler (MIXED)
**Purpose:** Interpretation, type checking, codegen, HIR/MIR passes
**Key Modules:** `interpreter`, `hir`, `mir`, `codegen`, `type_check`, `lint`, `formatter`
**Crate Type:** `["rlib", "staticlib", "cdylib"]`
**Dependencies:** 15+ crates (cranelift, inkwell, ash, etc.)
**Port Breakdown:**
- ✅ **Interpreter** — Tree-walking logic (Phase 3)
- ✅ **Type checking** — HM inference algorithms (Phase 3)
- ✅ **Lint** — Lint rules (Phase 2, already porting via EasyFix)
- ✅ **Formatter** — Code formatting (Phase 2)
- ✅ **HIR/MIR transforms** — IR passes (Phase 3)
- ❌ **Codegen** — Cranelift/LLVM backends (KEEP RUST)
**Lines:** ~40,000+ (50% portable)

### `wasm-runtime` - WASM Runtime (KEEP RUST)
**Purpose:** Execute WASM modules via Wasmer
**Verdict:** ❌ **MUST STAY RUST** — WASM VM integration

---

## Layer 5: High-Level Services (MOSTLY PORT)

### `db` - Database Abstraction (MIXED)
**Purpose:** Database drivers (libSQL, PostgreSQL)
**Port Potential:** 🟡 **MEDIUM** — Abstraction layer yes, drivers are Rust bindings
**Priority:** **Phase 4**

### `sqp` - Query/Persistence Layer (PORT TO SIMPLE) ⭐
**Purpose:** ORM-like query builder
**Dependencies:** `common`, `db`
**Port Potential:** ✅ **HIGH** — Query building logic
**Lines:** ~2,000
**Priority:** **Phase 2**

### `pkg` - Package Manager (PORT TO SIMPLE) ⭐
**Purpose:** Manifest parsing, dependency resolution, caching
**Key Modules:** `manifest`, `lock`, `resolver`, `cache`, `linker`
**Dependencies:** `toml`, `sdn`, `semver`, `indexmap`
**Port Potential:** ✅ **HIGH** — Dependency resolution algorithms
**Lines:** ~3,000
**Priority:** **Phase 1** (Quick Win)

### `ui` - TUI Framework (MIXED)
**Purpose:** Parse `.sui` templates, render TUI
**Port Potential:** 🟡 **MEDIUM** — Template parsing yes, rendering is FFI
**Priority:** **Phase 4**

### `lsp` - Language Server Protocol (PORT TO SIMPLE) ⭐
**Purpose:** LSP server for IDE integration
**Dependencies:** `common`, `parser`, `compiler`
**Port Potential:** ✅ **HIGH** — Protocol handling and analysis
**Lines:** ~5,000
**Priority:** **Phase 2**

### `dap` - Debug Adapter Protocol (PORT TO SIMPLE) ⭐
**Purpose:** DAP server for debugger integration
**Dependencies:** `common`, `parser`, `compiler`
**Port Potential:** ✅ **HIGH** — Protocol handling
**Lines:** ~3,000
**Priority:** **Phase 2**

---

## Layer 6: Top-Level Driver

### `driver` - Main Executable (PORT TO SIMPLE) ⭐⭐⭐
**Purpose:** CLI entry point, test runner, REPL, watcher, database trackers
**Binary:** `simple_runtime` (Rust runtime executes Simple apps)
**Key Modules:** `cli`, `interpreter`, `runner`, `simple_test`, `repl_runner_ffi`, `watcher`, `feature_db`, `test_db`, `bug_db`, `todo_db`, `task_db`
**Dependencies:** All other crates + 15+ external crates
**Port Potential:** ✅ **HIGH** — Most CLI logic, test running, DB management
**Lines:** ~10,000
**Priority:** **Phase 1** (Already migrating: "Main entry point is now Simple: src/app/cli/main.spl")
**Status:** 🔄 **IN PROGRESS** — CLI already ported to `src/app/cli/main.spl`

### `stub` - Settlement Stub (KEEP RUST)
**Purpose:** Minimal loader for standalone executables
**Binary:** `simple_stub_old`
**Verdict:** ❌ **MUST STAY RUST** — Executable loader and startup

---

## Testing & Utilities

### `util/arch_test` - Architecture Testing (PORT TO SIMPLE)
**Purpose:** Enforce architecture rules (dependency validation)
**Port Potential:** ✅ **HIGH** — Test framework logic
**Priority:** **Phase 2**

### `util/simple_mock_helper` - Coverage Tools (MIXED)
**Purpose:** Test coverage collection and reporting
**Port Potential:** 🟡 **MEDIUM** — Coverage analysis logic
**Priority:** **Phase 4**

---

## Dependency Graph (Bottom-Up)

```
Layer 0 (Foundation):
  hir-core [KEEP]

Layer 1 (Core):
  common [PARTIAL] -> hir-core
  sdn [PORT ⭐] -> hir-core
  type [PORT] -> parser

Layer 2 (Parser):
  parser [KEEP] -> common, hir-core
  dependency_tracker [PORT ⭐] -> common, parser
  diagnostics [PORT ⭐] -> hir-core

Layer 3 (Loaders - ALL KEEP):
  loader [KEEP] -> common
  native_loader [KEEP] -> common, runtime
  simd [KEEP] -> common
  gpu [KEEP] -> common
  embedded [KEEP] (no deps)

Layer 4 (Compilation):
  runtime [KEEP] -> common, sdn, loader, hir-core
  compiler [MIXED] -> ALL Layer 1-3
  wasm-runtime [KEEP] -> runtime, common

Layer 5 (Services):
  db [MIXED] -> common
  sqp [PORT ⭐] -> common, db
  pkg [PORT ⭐] -> sdn
  ui [MIXED] -> parser, runtime
  lsp [PORT ⭐] -> common, parser, compiler
  dap [PORT ⭐] -> common, parser, compiler

Layer 6 (Driver):
  driver [PORT ⭐⭐⭐] -> ALL
  stub [KEEP] -> loader
```

---

## Migration Phases for v0.4.0

### Phase 1: Quick Wins (Low Dependencies)
**Target:** 4 crates, ~15,000 lines

1. **`sdn`** — Self-contained parser
   - No dependencies on other ported crates
   - Pure logic, no FFI
   - Estimated: 2 weeks

2. **`diagnostics`** — Error formatting
   - Minimal dependencies
   - i18n integration already in place
   - Estimated: 1 week

3. **`pkg`** — Package manager
   - Depends on `sdn` (ported in Phase 1)
   - Dependency resolution algorithms
   - Estimated: 3 weeks

4. **`driver` CLI/test/DB** — High-level driver logic
   - Already partially migrated (`src/app/cli/main.spl`)
   - Test runner, database trackers
   - Estimated: 4 weeks

**Phase 1 Total:** ~10 weeks

### Phase 2: Analysis & Tooling
**Target:** 5 crates, ~15,000 lines

1. **`lsp`** — Language server
   - Protocol handling
   - Estimated: 4 weeks

2. **`dap`** — Debug adapter
   - Protocol handling
   - Estimated: 3 weeks

3. **`compiler/lint`** — Lint framework
   - Already porting via EasyFix
   - Estimated: 2 weeks

4. **`compiler/formatter`** — Code formatter
   - AST traversal and pretty-printing
   - Estimated: 3 weeks

5. **`sqp`** — Query layer
   - ORM-like query building
   - Estimated: 2 weeks

**Phase 2 Total:** ~14 weeks

### Phase 3: Core Compilation Logic
**Target:** 4 crates/modules, ~20,000 lines

1. **`dependency_tracker`** — Module resolution
   - Graph algorithms
   - Estimated: 3 weeks

2. **`compiler/interpreter`** — Tree-walking interpreter
   - Pure logic, no FFI
   - Estimated: 5 weeks

3. **`compiler/type_check`** — Type inference
   - HM inference algorithms
   - Estimated: 6 weeks

4. **`compiler/hir`, `compiler/mir`** — IR transforms
   - AST lowering and optimization passes
   - Estimated: 4 weeks

**Phase 3 Total:** ~18 weeks

### Phase 4: Remaining (Optional)
**Target:** 3 crates, ~5,000 lines

1. **`type`** — Type utilities
2. **`ui` (partial)** — Template parsing
3. **`db` (partial)** — Abstraction layer

**Phase 4 Total:** ~6 weeks

---

## Summary Statistics

### Crate Classification

| Category | Count | % |
|----------|-------|---|
| **Must Stay Rust** | 10 | 40% |
| **High Port Potential** | 12 | 48% |
| **Medium Port (Mixed)** | 3 | 12% |
| **Total** | 25 | 100% |

### Lines of Code (Estimated)

| Category | Lines | % of Total |
|----------|-------|-----------|
| Must Stay Rust | ~50,000 | 30% |
| Can Port | ~115,000 | 70% |
| **Total Codebase** | ~165,000 | 100% |

**Note:** High-level logic is typically more verbose than low-level code, so porting 48% of crates = ~70% of lines.

### v0.4.0 Target

- **Phases 1-3:** Port 13 crates = 52% of crates, ~65% of lines
- **Estimated Effort:** 42 weeks (10 + 14 + 18)
- **Timeline:** Q1-Q2 2026 (with parallel work)

---

## Critical Paths

### Cannot Port Until These Are Done

1. **`sdn` must port first** → Blocks `pkg`
2. **`parser` stays Rust** → All parsing-dependent ports use FFI
3. **`runtime` stays Rust** → All FFI-dependent code must bridge
4. **`compiler/codegen` stays Rust** → Backend-dependent features stay Rust

### Recommended Parallelization

**Sprint 1 (Parallel):**
- `sdn` + `diagnostics` (no interdependencies)

**Sprint 2 (Sequential after Sprint 1):**
- `pkg` (depends on `sdn`)
- `driver` CLI (depends on `pkg`, `diagnostics`)

**Sprint 3 (Parallel):**
- `lsp` + `dap` + `compiler/lint` (independent)

**Sprint 4 (Sequential):**
- `compiler/interpreter` → `compiler/type_check` (depend on each other)

---

## FFI Bridge Strategy

### Rust → Simple Calls
Already working via `simple_runtime` executable:
```rust
// Rust calls Simple code
runtime.load("src/app/cli/main.spl");
runtime.call_main(args);
```

### Simple → Rust Calls
Use `extern fn` declarations:
```simple
# In Simple code
extern fn rt_file_read_text(path: text) -> text?
extern fn rt_dict_new() -> Dict<Any, Any>

# Implementation stays in Rust runtime
```

### Mixed Module Pattern
For `compiler` crate with mixed portability:
1. Port `interpreter`, `type_check`, `lint`, `formatter` to Simple
2. Keep `codegen` in Rust (Cranelift/LLVM FFI)
3. Bridge via FFI: Simple calls Rust codegen backend

---

## Risk Mitigation

### Performance Concerns
- **Parser stays Rust** — Proven critical path
- **Runtime stays Rust** — Memory management, GC
- **Codegen stays Rust** — Backend complexity
- **Accept tradeoffs** — 2-3x slowdown in ported logic acceptable (CLI, lint, etc.)

### Incremental Migration
- Port module-by-module, not all at once
- Keep Rust version as fallback until Simple version proven
- Feature flags to toggle implementations

### Testing Strategy
- Bootstrap verification after each major port
- Performance benchmarks before/after
- Maintain 100% test coverage

---

## Conclusion

**v0.4.0 Goal:** Port 52% of crates (65% of code) to Simple while keeping critical low-level infrastructure in Rust.

**Key Wins:**
- Dogfooding: Most of compiler written in Simple
- Maintainability: High-level logic easier to read/modify
- Self-hosting: Compiler compiles most of itself
- Performance: Keep hot paths in Rust

**Timeline:** 42 weeks estimated, target Q2 2026 with parallel execution.
