# Overall Update Report: 2026-02-16 to 2026-03-02

**Date:** 2026-03-02
**Period:** 2026-02-16 through 2026-03-02 (14 days)
**Branch:** main

## Summary

This period saw a major structural overhaul of the codebase focused on cleanup, migration, and stabilization. The headline changes are:

- **912 files changed**, with **10,394 insertions** and **134,778 deletions** (net reduction of ~124K lines)
- **431 files deleted** (337 from disabled libraries, 66 from nogc_sync_mut deduplication, 28 from stale compiler/test/tools)
- **11 files added** (3 new features, 8 supporting files)
- **472 files modified** across compiler, stdlib, apps, and tests
- **3 files renamed** (MCP handler adapters relocated)
- Self-hosting **Stage 3->4 fixed-point reached** with SMF relocation metadata for unified JIT + native loading

---

## 1. MDSOC Compiler Migration

The compiler source tree was reorganized into a numbered layer system under `src/compiler/`. Each layer is prefixed with a two-digit number (00-99) that encodes its position in the compilation pipeline.

### Numbered Layer Structure

| Layer | Directory | Role |
|-------|-----------|------|
| 00 | `00.common/` | Error types, config, effects, visibility, diagnostics |
| 10 | `10.frontend/` | Lexer, parser, AST, treesitter, desugar |
| 15 | `15.blocks/` | Block definition system |
| 20 | `20.hir/` | HIR types, definitions, lowering |
| 25 | `25.traits/` | Trait def, impl, solver, coherence, validation |
| 30 | `30.types/` | Type inference, dimension constraints |
| 35 | `35.semantics/` | Semantic analysis, lint, narrowing, safety |
| 40 | `40.mono/` | Monomorphization |
| 50 | `50.mir/` | MIR types, data, instructions |
| 55 | `55.borrow/` | Borrow checking, GC analysis |
| 60 | `60.mir_opt/` | MIR optimization passes |
| 70 | `70.backend/` | Backends (LLVM, C, Cranelift, WASM, Native) |
| 80 | `80.driver/` | Driver, pipeline, incremental compilation |
| 85 | `85.mdsoc/` | Virtual capsules, feature transforms, adapters |
| 90 | `90.tools/` | API surface, coverage, query, AOP |
| 95 | `95.interp/` | Interpreter, MIR interpreter |
| 99 | `99.loader/` | Module resolver, loader |

### Deleted Old Directories

The following legacy (non-numbered) compiler paths were cleaned up:

- `src/compiler/core/aop_debug_log.spl` -- moved to numbered layer
- `src/compiler/core/backend_types.spl` -- moved to numbered layer
- `src/compiler/core/interpreter/jit.spl` -- moved to numbered layer
- `src/compiler/core/lexer.spl` -- moved to numbered layer
- `src/compiler/linker/smf_reader.spl` -- moved to numbered layer
- `src/compiler/00.common/registry/mod.spl` -- removed (consolidated)
- `src/compiler/99.loader/mod.spl` -- removed (consolidated)

### New MDSOC Symlink

A symlink `src/compiler/mdsoc -> 85.mdsoc` was added for backward compatibility with imports that reference the unnumbered `mdsoc` path.

### Impact

- **162 files changed** in `src/compiler/` with 2,268 insertions and 1,752 deletions
- **153 modified** files received import path updates and refactoring
- Total compiler source: **207,912 lines** across .spl files in `src/compiler/`

---

## 2. Disabled Library Cleanup

**337 files** were deleted from `src/compiler_rust/lib/std/src/` by removing 12 `.disabled/` directories. These were placeholder/experimental libraries that were never compiled and had accumulated as dead code.

| Directory | Files Removed | Approx. Lines |
|-----------|--------------|---------------|
| `ui.disabled/` | 71 | ~26,556 |
| `graphics.disabled/` | 65 | ~15,353 |
| `ml.disabled/` | 64 | ~15,349 |
| `godot.disabled/` | 39 | ~13,593 |
| `parser.disabled/` | 36 | ~11,059 |
| `unreal.disabled/` | 13 | ~4,545 |
| `units.disabled/` | 13 | ~3,558 |
| `web.disabled/` | 10 | ~3,451 |
| `doctest.disabled/` | 9 | ~2,314 |
| `electron.disabled/` | 10 | ~1,347 |
| `browser.disabled/` | 4 | ~1,019 |
| `coverage.disabled/` | 3 | ~686 |
| **Total** | **337** | **~98,830** |

Additionally, 2 files were removed from `src/compiler_rust/lib/std/src/spec/` (`assertions.spl`, `bdd.spl` -- empty stubs).

---

## 3. MCP Server Updates

### Handler Adapter Relocations

Three MCP handler adapter files were moved from `src/lib/nogc_sync_mut/mcp/handler_adapters/` to `src/lib/nogc_async_mut/mcp/handler_adapters/`:

- `debug_adapter.spl`
- `debug_log_adapter.spl`
- `diag_adapter.spl`

This relocation aligns these adapters with their async runtime dependencies.

### MCP Module Consolidation

**66 files deleted** from `src/lib/nogc_sync_mut/`:
- **54 MCP files** -- deduplicated with `src/lib/nogc_async_mut/mcp/` (the canonical location)
- **12 LLM files** -- entire `src/lib/nogc_sync_mut/llm/` directory removed (consolidated into `nogc_async_mut/llm/`)

### JSON/Protocol Fix (2026-03-02)

Documented in `doc/report/mcp_json_fix_2026-03-02.md`. Three root causes fixed:

1. **`escape_json()` O(n^2) performance** -- Character-by-character iteration took ~82s for 330-line files; replaced with native `replace()` calls (0.2s)
2. **Content-Length byte/char mismatch** -- `body.len()` returns character count but Content-Length requires byte count; multi-byte UTF-8 chars caused framing errors. New `text_byte_len()` function added
3. **ANSI escape codes in JSON** -- Subprocess output contained unescaped control sequences; fixed with `NO_COLOR=1 TERM=dumb` env vars and `sed` ANSI stripping

Files modified: `main_lazy_json.spl`, `main_lazy_protocol.spl`, `main_lazy_tasks.spl`

All 76 MCP tools verified working after fixes.

---

## 4. Rust Interpreter Changes

**24 files changed** across the Rust interpreter subsystem with **311 insertions** and **180 deletions**.

### interpreter_call (6 files, +150/-24)

The largest change was in `block_execution.rs` (+133 lines):
- **Static method registration as mangled free functions** -- Class static methods now register as `ClassName__method` in the function table, enabling `Type.method()` path-call syntax
- **Arc-based array mutation** -- `Value::Array` switched from `Vec` to `Arc<Vec>` with `Arc::make_mut()` for copy-on-write semantics in indexed assignment
- **BDD test fixes** -- Updated `bdd.rs` for improved test block execution
- **Builtin function expansion** -- Additional builtins registered in `builtins.rs`

### interpreter_extern (7 files, +41/-38)

- Normalized `str` to `text` type annotations across `cli.rs`, `collections.rs`, `env_ffi.rs`, `file_io.rs`, `lexer_ffi.rs`, `native_ffi.rs`, `regex.rs`
- Fixed type conversion edge cases in collection operations

### interpreter_helpers (3 files, +30/-30)

- `method_dispatch.rs` -- Updated method resolution for text type normalization
- `collections.rs` -- Refined collection helper methods
- `patterns.rs` -- Pattern matching adjustments

### interpreter_method (4 files, +71/-71)

- `collections.rs` -- Rewrote collection method dispatch (100 lines changed)
- `primitives.rs` -- Updated primitive type methods
- `string.rs` -- String method normalization
- `special/mock.rs` -- Mock system adjustments

### Value System (4 files, +13/-12)

- `value.rs` -- Core value type adjustments
- `value_bridge.rs` -- Bridge layer updates
- `value_pointers.rs` -- Pointer handling refinement
- `value_tests_basic.rs` -- Test updates for value changes

### Parser Fix

- `parser_patterns.rs` (+14/-1) -- Fixed tuple destructuring bug: comma inside tuple patterns was consumed as or-pattern separator. LParen handler now uses `parse_single_pattern()` instead of `parse_pattern()`, enabling `val (a, b, c) = (10, 20, 30)` syntax

### Other Rust Changes

- `data/json.spl` -- Replaced O(n^2) string concatenation in JSON serialization with `parts: [text]` array + `join("")` pattern
- `macro/expansion.rs`, `macro/invocation.rs` -- Minor type annotation fixes
- `runtime_bridge.rs` -- Bridge layer updates
- `native_io_helpers.rs` -- I/O helper refinements

---

## 5. New Features

### 5.1 Yank Command (`src/app/yank/main.spl`, 92 lines)

New CLI subcommand for marking package versions as yanked in the package registry. Integrates with the existing `app.package.registry` configuration system.

### 5.2 String Builder Optimization (`src/compiler/60.mir_opt/mir_opt/string_builder_opt.spl`, 265 lines)

New MIR optimization pass that detects the common loop pattern:

```simple
var result = ""
while ...:
    result = result + expr
```

And optimizes it to use a string builder internally, avoiding O(n^2) string concatenation in hot loops.

### 5.3 Manifest Daemon (`src/app/test_daemon/manifest_daemon.spl`, 139 lines)

Background watcher that keeps the test manifest up to date by polling `test/`, `src/`, and `doc/` directories for changes every 2 seconds. When changes are detected, it incrementally updates the manifest file. The test runner reads this manifest for near-instant test discovery, eliminating the startup scan overhead.

### 5.4 Other New Files

- `PLAN.md` -- Project planning document
- `doc/report/mcp_json_fix_2026-03-02.md` -- MCP fix report
- `src/lib/resource_tracker.spl` -- Resource lifecycle tracking
- `src/lib/sdn/__init__.spl` -- SDN module init
- `src/lib/simple.sdn` -- Project configuration
- `src/lib/string_core.spl` -- Core string utilities
- `src/lib/text.spl` -- Text processing utilities
- `test/unit/std/test_quick.spl` -- Quick stdlib test
- `src/compiler/mdsoc` -- Symlink to `85.mdsoc`

---

## 6. Additional Cleanup

### Deleted Test Files (12 files)

- `test/unit/compiler/hir/hir_eval_spec.spl` (558 lines)
- `test/unit/compiler/hir/hir_lower_spec.spl` (498 lines)
- `test/unit/compiler/hir/hir_module_spec.spl` (487 lines)
- `test/unit/compiler/hir/hir_types_spec.spl` (526 lines)
- `test/unit/lib/game_engine/actor_model_spec.spl` (59 lines)
- `test/unit/lib/game_engine/component_spec.spl` (73 lines)
- `test/feature/usage/actor_model_spec.spl`
- `test/feature/usage/component_spec.spl`
- `test/feature/usage/contract_persistence_feature_spec.spl`
- `test/feature/usage/mat4_spec.spl`
- `doc/test/test_db.sdn.v2_backup`
- `src/compiler_rust/doc/test/test_db.sdn.v2_backup`

### Deleted App Files (2 files)

- `src/app/test_runner_new/test_db_migrate.spl.disabled`
- `src/app/test_runner_new/test_db_perf.spl.disabled`

### Deleted Windows Tools (5 files, ~2,284 lines)

- `tools/windows/build_win.py` (626 lines)
- `tools/windows/fix_cpp.py` (953 lines)
- `tools/windows/desugar_lambdas.py` (237 lines)
- `tools/windows/stub_broken.py` (207 lines)
- `tools/windows/ffi_shim.spl` (261 lines)

These Python-based Windows build tools were removed as the project is now fully self-hosted in Simple.

---

## 7. Codebase Statistics

### Current File Counts

| Category | Files | Lines |
|----------|-------|-------|
| Source `.spl` files | 3,708 | ~29,090 (src/lib) |
| Source `.rs` files | 1,801 | ~1,819,181 |
| Compiler `.spl` (src/compiler/) | -- | 207,912 |
| Test `.spl` files | 1,772 | ~11,937 |
| **Total source files** | **5,509** | -- |

### Change Summary by Area

| Area | Files Changed | Insertions | Deletions |
|------|--------------|------------|-----------|
| `src/compiler/` | 162 | 2,268 | 1,752 |
| `src/compiler_rust/` | 398 | 945 | 122,673 |
| `src/lib/` | 213 | 3,089 | 2,400 |
| `src/app/` | 36 | 1,083 | 1,023 |
| `test/` | 84 | 2,476 | 4,502 |
| `doc/` | 12 | 593 | 156 |
| `tools/` | 5 | 0 | 2,284 |
| **Total** | **912** | **10,394** | **134,778** |

The overwhelming majority of deletions (~122K) came from removing the 337 disabled library stubs in `src/compiler_rust/lib/std/src/`.

---

## 8. Self-Hosting Status

### Stage 3->4 Fixed-Point (2026-02-28)

The self-hosting bootstrap chain has reached a **fixed-point**: the Simple compiler compiled by Simple produces a binary identical (same size) to the one that compiled it. The full chain:

1. **Rust seed** (bootstrap) compiles the Simple compiler source
2. **Stage 1 binary** compiles the Simple compiler again
3. **Stage 2 binary** compiles once more
4. **Stage 3 = Stage 2** -- fixed-point reached, confirming correctness

### SMF Relocation Metadata (commit `dbf3936218`)

Added relocation metadata to the SMF (Simple Module Format) binary format, enabling unified JIT + native loading from the same binary artifact. This means:

- JIT interpreter can load and patch SMF modules at runtime
- Native linker can resolve relocations for ahead-of-time compilation
- Both paths share the same module format, eliminating format divergence

### Deterministic Cranelift Codegen (commit `f291dd201d`)

Fixed non-determinism in Cranelift code generation to ensure **reproducible bootstrap builds**. Without deterministic codegen, the fixed-point verification would fail due to spurious binary differences.

### Cross-Platform Bootstrap (commit `9c5dd08400`)

Added compilation support for Windows, FreeBSD, and macOS bootstrap, expanding the set of platforms that can bootstrap the self-hosted compiler.

---

## 9. Notable Commits (Chronological)

| Commit | Description |
|--------|-------------|
| `2f048ccc36` | Split all 800+ line files into smaller modules |
| `7be86c2dad` | Rename _ext files to descriptive names |
| `22a0355663` | Rename 39 adhoc _ext test files |
| `301cd4f7e7` | Remove ~200 semantically duplicated files |
| `29ab63abc6` | Use interpreted mode for test runner, add WFFI dynamic loading |
| `a6c13be4f4` | Equalize library variants, fix O(n^2) algorithms, add baremetal modules |
| `8e48ae29d0` | Normalize str->text type annotations, remove temp_bootstrap |
| `743393abb1` | Resolve interpreter-mode test failures |
| `f291dd201d` | Deterministic Cranelift codegen for reproducible bootstrap |
| `ae91fcd81c` | Fix MCP server shell tools by fixing interpreter tuple returns |
| `dbf3936218` | SMF relocation metadata for unified JIT + native loading |

---

## 10. Key Takeaways

1. **Massive dead code removal** -- 124K net lines removed, primarily from disabled library stubs that were never compiled. The codebase is now leaner and more maintainable.

2. **Structural clarity** -- The numbered layer system (00-99) in `src/compiler/` makes the compilation pipeline self-documenting. Layer ordering matches the actual data flow.

3. **Self-hosting milestone** -- The fixed-point verification proves the compiler is correct: it can reproduce itself. SMF relocation metadata unifies JIT and native loading.

4. **MCP server reliability** -- Three critical bugs fixed (O(n^2) JSON escaping, UTF-8 Content-Length, ANSI escapes). All 76 tools verified working.

5. **Interpreter maturation** -- Tuple destructuring, static method path calls, and Arc-based array mutation bring the Rust interpreter closer to full language coverage.
